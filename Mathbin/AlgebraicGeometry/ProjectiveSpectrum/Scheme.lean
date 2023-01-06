/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebraic_geometry.projective_spectrum.scheme
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathbin.AlgebraicGeometry.SpecCat
import Mathbin.RingTheory.GradedAlgebra.Radical

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `to_Spec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `Proj_iso_Spec_Top_component.to_Spec.carrier`). This ideal is
    prime, the proof is in `Proj_iso_Spec_Top_component.to_Spec.to_fun`. The fact that this function
    is continuous is found in `Proj_iso_Spec_Top_component.to_Spec`
  - backward direction `from_Spec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal`;
    * This ideal is also homogeneous, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.prime`.
    Hence we have a well defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `Proj_iso_Spec_Top_component.from_Spec.to_fun`. But to prove the continuity of this function,
    we need to prove `from_Spec ∘ to_Spec` and `to_Spec ∘ from_Spec` are both identities (TBC).

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Proj_iso_Spec_Top_component.to_Spec`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Proj_iso_Spec_Top_component.to_Spec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

namespace AlgebraicGeometry

open DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {R A : Type _}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- mathport name: exprProj
local notation "Proj" => ProjCat.toLocallyRingedSpace 𝒜

-- mathport name: «exprProj.T»
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(str "\"Proj.T\"")]
     "=>"
     (Term.proj
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
        "."
        (fieldIdx "1"))
       "."
       (fieldIdx "1"))
      "."
      (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.proj
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
         "."
         (fieldIdx "1"))
        "."
        (fieldIdx "1"))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
        "."
        (fieldIdx "1"))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.11'-/-- failed to format: format: uncaught backtrack exception
local notation "Proj.T" => Proj . 1 . 1 . 1

-- mathport name: «exprProj| »
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(str "\"Proj| \"") (Command.identPrec `U [])]
     "=>"
     (Term.app
      (Term.proj
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
       "."
       `restrict)
      [(Term.app
        `Opens.open_embedding
        [(Term.typeAscription
          "("
          `U
          ":"
          [(Term.app
            `Opens
            [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
              "Proj.T")])]
          ")")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
        "."
        `restrict)
       [(Term.app
         `Opens.open_embedding
         [(Term.typeAscription
           "("
           `U
           ":"
           [(Term.app
             `Opens
             [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
               "Proj.T")])]
           ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Opens.open_embedding
       [(Term.typeAscription
         "("
         `U
         ":"
         [(Term.app
           `Opens
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `U
       ":"
       [(Term.app
         `Opens
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Opens
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj.T._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.505'-/-- failed to format: format: uncaught backtrack exception
local notation "Proj| " U => Proj . restrict Opens.open_embedding ( U : Opens Proj.T )

-- mathport name: «exprProj.T| »
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(str "\"Proj.T| \"") (Command.identPrec `U [])]
     "=>"
     (Term.proj
      (Term.proj
       (Term.proj
        (Term.app
         (Term.proj
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
          "."
          `restrict)
         [(Term.app
           `Opens.open_embedding
           [(Term.typeAscription
             "("
             `U
             ":"
             [(Term.app
               `Opens
               [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
                 "Proj.T")])]
             ")")])])
        "."
        `toSheafedSpace)
       "."
       `toPresheafedSpace)
      "."
      (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.proj
         (Term.app
          (Term.proj
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
           "."
           `restrict)
          [(Term.app
            `Opens.open_embedding
            [(Term.typeAscription
              "("
              `U
              ":"
              [(Term.app
                `Opens
                [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
                  "Proj.T")])]
              ")")])])
         "."
         `toSheafedSpace)
        "."
        `toPresheafedSpace)
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (Term.app
         (Term.proj
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
          "."
          `restrict)
         [(Term.app
           `Opens.open_embedding
           [(Term.typeAscription
             "("
             `U
             ":"
             [(Term.app
               `Opens
               [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
                 "Proj.T")])]
             ")")])])
        "."
        `toSheafedSpace)
       "."
       `toPresheafedSpace)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
         "."
         `restrict)
        [(Term.app
          `Opens.open_embedding
          [(Term.typeAscription
            "("
            `U
            ":"
            [(Term.app
              `Opens
              [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
                "Proj.T")])]
            ")")])])
       "."
       `toSheafedSpace)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj "Proj")
        "."
        `restrict)
       [(Term.app
         `Opens.open_embedding
         [(Term.typeAscription
           "("
           `U
           ":"
           [(Term.app
             `Opens
             [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»
               "Proj.T")])]
           ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Opens.open_embedding
       [(Term.typeAscription
         "("
         `U
         ":"
         [(Term.app
           `Opens
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `U
       ":"
       [(Term.app
         `Opens
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Opens
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T» "Proj.T")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj.T._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.505'-/-- failed to format: format: uncaught backtrack exception
local
  notation
  "Proj.T| " U
  =>
  Proj . restrict Opens.open_embedding ( U : Opens Proj.T ) . toSheafedSpace . toPresheafedSpace . 1

-- mathport name: «exprpbo »
-- the underlying topological space of `Proj` restricted to some open set
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

-- mathport name: «exprsbo »
-- basic open sets in `Proj`
local notation "sbo " f => PrimeSpectrum.basicOpen f

-- mathport name: «exprSpec »
-- basic open sets in `Spec`
local notation "Spec " ring => SpecCat.locallyRingedSpaceObj (CommRingCat.of Ring)

-- mathport name: «exprSpec.T »
-- `Spec` as a locally ringed space
local notation "Spec.T " ring =>
  (SpecCat.locallyRingedSpaceObj (CommRingCat.of Ring)).toSheafedSpace.toPresheafedSpace.1

-- mathport name: «exprA⁰_ »
-- the underlying topological space of `Spec`
local notation "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f

namespace ProjIsoSpecTopComponent

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/
namespace ToSpec

open Ideal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder "{" [`𝒜] [] "}")
      (Term.implicitBinder "{" [`f] [":" `A] "}")
      (Term.implicitBinder "{" [`m] [":" (termℕ "ℕ")] "}")
      (Term.explicitBinder "(" [`f_deg] [":" («term_∈_» `f "∈" (Term.app `𝒜 [`m]))] [] ")")
      (Term.explicitBinder
       "("
       [`x]
       [":"
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj|_»
         "Proj| "
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj|_»
       "Proj| "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj|_»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj|_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.544'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { 𝒜 } { f : A } { m : ℕ } ( f_deg : f ∈ 𝒜 m ) ( x : Proj| pbo f )

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal\nis prime is proven in `Top_component.forward.to_fun`-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `carrier [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `Ideal
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Ideal.comap
        [(Term.app
          `algebraMap
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
           (Term.app `Away [`f])])
         («term_<|_»
          `Ideal.span
          "<|"
          (Set.Data.Set.Image.term_''_
           (Term.app `algebraMap [`A (Term.app `Away [`f])])
           " '' "
           (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal)))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.comap
       [(Term.app
         `algebraMap
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
          (Term.app `Away [`f])])
        («term_<|_»
         `Ideal.span
         "<|"
         (Set.Data.Set.Image.term_''_
          (Term.app `algebraMap [`A (Term.app `Away [`f])])
          " '' "
          (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `Ideal.span
       "<|"
       (Set.Data.Set.Image.term_''_
        (Term.app `algebraMap [`A (Term.app `Away [`f])])
        " '' "
        (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app `algebraMap [`A (Term.app `Away [`f])])
       " '' "
       (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `val)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `algebraMap [`A (Term.app `Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Ideal.span
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `Ideal.span
      "<|"
      (Set.Data.Set.Image.term_''_
       (Term.app `algebraMap [`A (Term.paren "(" (Term.app `Away [`f]) ")")])
       " '' "
       (Term.proj (Term.proj `x "." `val) "." `asHomogeneousIdeal)))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `algebraMap
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
        (Term.app `Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
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
    For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
    is prime is proven in `Top_component.forward.to_fun`-/
  def
    carrier
    : Ideal A⁰_ f
    :=
      Ideal.comap
        algebraMap A⁰_ f Away f Ideal.span <| algebraMap A Away f '' x . val . asHomogeneousIdeal
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_carrier_iff [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`z]
         [":" (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `z "∈" (Term.app `carrier [`𝒜 `x]))
         "↔"
         («term_∈_»
          (Term.proj `z "." `val)
          "∈"
          (Term.app
           `Ideal.span
           [(Set.Data.Set.Image.term_''_
             (Term.app `algebraMap [`A (Term.app `Away [`f])])
             " '' "
             (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))])))))
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
       («term_∈_» `z "∈" (Term.app `carrier [`𝒜 `x]))
       "↔"
       («term_∈_»
        (Term.proj `z "." `val)
        "∈"
        (Term.app
         `Ideal.span
         [(Set.Data.Set.Image.term_''_
           (Term.app `algebraMap [`A (Term.app `Away [`f])])
           " '' "
           (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.proj `z "." `val)
       "∈"
       (Term.app
        `Ideal.span
        [(Set.Data.Set.Image.term_''_
          (Term.app `algebraMap [`A (Term.app `Away [`f])])
          " '' "
          (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.span
       [(Set.Data.Set.Image.term_''_
         (Term.app `algebraMap [`A (Term.app `Away [`f])])
         " '' "
         (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app `algebraMap [`A (Term.app `Away [`f])])
       " '' "
       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `algebraMap [`A (Term.app `Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Term.app `algebraMap [`A (Term.paren "(" (Term.app `Away [`f]) ")")])
      " '' "
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj `z "." `val)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∈_» `z "∈" (Term.app `carrier [`𝒜 `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier [`𝒜 `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
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
  mem_carrier_iff
  ( z : A⁰_ f )
    : z ∈ carrier 𝒜 x ↔ z . val ∈ Ideal.span algebraMap A Away f '' x . 1 . asHomogeneousIdeal
  := Iff.rfl
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mem_carrier_iff

theorem MemCarrier.clear_denominator' [DecidableEq (Away f)] {z : Localization.Away f}
    (hz : z ∈ span (algebraMap A (Away f) '' x.val.asHomogeneousIdeal)) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f)(N : ℕ)(acd :
      ∀ y ∈ c.support.image c, A),
      f ^ N • z =
        algebraMap A (Away f)
          (∑ i in c.support.attach,
            acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.some) :=
  by
  rw [← submodule_span_eq, Finsupp.span_eq_range_total, LinearMap.mem_range] at hz
  rcases hz with ⟨c, eq1⟩
  rw [Finsupp.total_apply, Finsupp.sum] at eq1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers f) (c.support.image c)
  choose acd hacd using hN
  refine' ⟨c, N, acd, _⟩
  rw [← eq1, smul_sum, map_sum, ← sum_attach]
  congr 1
  ext i
  rw [_root_.map_mul, hacd, (Classical.choose_spec i.1.2).2, smul_eq_mul, smul_mul_assoc]
  rfl
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier.clear_denominator' AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.MemCarrier.clear_denominator'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `MemCarrier.clear_denominator [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [(Term.app `Away [`f])]) "]")
        (Term.implicitBinder
         "{"
         [`z]
         [":" (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
         "}")
        (Term.explicitBinder "(" [`hz] [":" («term_∈_» `z "∈" (Term.app `carrier [`𝒜 `x]))] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `c)]
            ":"
            (Data.Finsupp.Defs.«term_→₀_»
             (Set.Data.Set.Image.term_''_
              (Term.app `algebraMap [`A (Term.app `Away [`f])])
              " '' "
              (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
             " →₀ "
             (Term.app `Away [`f]))
            ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `N)] ":" (termℕ "ℕ") ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `acd)]
            ":"
            (Std.ExtendedBinder.«term∀__,_»
             "∀"
             (Lean.binderIdent `y)
             («binderTerm∈_» "∈" (Term.app (Term.proj (Term.proj `c "." `support) "." `image) [`c]))
             ","
             `A)
            ")")])
         ","
         («term_=_»
          (Algebra.Group.Defs.«term_•_» («term_^_» `f "^" `N) " • " (Term.proj `z "." `val))
          "="
          (Term.app
           `algebraMap
           [`A
            (Term.app `Away [`f])
            (BigOperators.Algebra.BigOperators.Basic.finset.sum
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             " in "
             (Term.proj (Term.proj `c "." `support) "." `attach)
             ", "
             («term_*_»
              (Term.app
               `acd
               [(Term.app `c [`i])
                (Term.app
                 (Term.proj `Finset.mem_image "." `mpr)
                 [(Term.anonymousCtor
                   "⟨"
                   [`i
                    ","
                    (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
                   "⟩")])])
              "*"
              (Term.proj
               (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2"))
               "."
               `some)))])))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `MemCarrier.clear_denominator' [`x])
        "<|"
        (Term.app (Term.proj (Term.app `mem_carrier_iff [`𝒜 `x `z]) "." `mpr) [`hz]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `MemCarrier.clear_denominator' [`x])
       "<|"
       (Term.app (Term.proj (Term.app `mem_carrier_iff [`𝒜 `x `z]) "." `mpr) [`hz]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `mem_carrier_iff [`𝒜 `x `z]) "." `mpr) [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `mem_carrier_iff [`𝒜 `x `z]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mem_carrier_iff [`𝒜 `x `z])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_carrier_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mem_carrier_iff [`𝒜 `x `z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `MemCarrier.clear_denominator' [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MemCarrier.clear_denominator'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `c)]
          ":"
          (Data.Finsupp.Defs.«term_→₀_»
           (Set.Data.Set.Image.term_''_
            (Term.app `algebraMap [`A (Term.app `Away [`f])])
            " '' "
            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
           " →₀ "
           (Term.app `Away [`f]))
          ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `N)] ":" (termℕ "ℕ") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `acd)]
          ":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `y)
           («binderTerm∈_» "∈" (Term.app (Term.proj (Term.proj `c "." `support) "." `image) [`c]))
           ","
           `A)
          ")")])
       ","
       («term_=_»
        (Algebra.Group.Defs.«term_•_» («term_^_» `f "^" `N) " • " (Term.proj `z "." `val))
        "="
        (Term.app
         `algebraMap
         [`A
          (Term.app `Away [`f])
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           (Term.proj (Term.proj `c "." `support) "." `attach)
           ", "
           («term_*_»
            (Term.app
             `acd
             [(Term.app `c [`i])
              (Term.app
               (Term.proj `Finset.mem_image "." `mpr)
               [(Term.anonymousCtor
                 "⟨"
                 [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
                 "⟩")])])
            "*"
            (Term.proj
             (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2"))
             "."
             `some)))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_•_» («term_^_» `f "^" `N) " • " (Term.proj `z "." `val))
       "="
       (Term.app
        `algebraMap
        [`A
         (Term.app `Away [`f])
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.proj (Term.proj `c "." `support) "." `attach)
          ", "
          («term_*_»
           (Term.app
            `acd
            [(Term.app `c [`i])
             (Term.app
              (Term.proj `Finset.mem_image "." `mpr)
              [(Term.anonymousCtor
                "⟨"
                [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
                "⟩")])])
           "*"
           (Term.proj
            (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2"))
            "."
            `some)))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `algebraMap
       [`A
        (Term.app `Away [`f])
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.proj (Term.proj `c "." `support) "." `attach)
         ", "
         («term_*_»
          (Term.app
           `acd
           [(Term.app `c [`i])
            (Term.app
             (Term.proj `Finset.mem_image "." `mpr)
             [(Term.anonymousCtor
               "⟨"
               [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
               "⟩")])])
          "*"
          (Term.proj (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2")) "." `some)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.proj (Term.proj `c "." `support) "." `attach)
       ", "
       («term_*_»
        (Term.app
         `acd
         [(Term.app `c [`i])
          (Term.app
           (Term.proj `Finset.mem_image "." `mpr)
           [(Term.anonymousCtor
             "⟨"
             [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
             "⟩")])])
        "*"
        (Term.proj (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2")) "." `some)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app
        `acd
        [(Term.app `c [`i])
         (Term.app
          (Term.proj `Finset.mem_image "." `mpr)
          [(Term.anonymousCtor
            "⟨"
            [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
            "⟩")])])
       "*"
       (Term.proj (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2")) "." `some))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2")) "." `some)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `i "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `acd
       [(Term.app `c [`i])
        (Term.app
         (Term.proj `Finset.mem_image "." `mpr)
         [(Term.anonymousCtor
           "⟨"
           [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
           "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Finset.mem_image "." `mpr)
       [(Term.anonymousCtor
         "⟨"
         [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Finset.mem_image "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Finset.mem_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `Finset.mem_image "." `mpr)
      [(Term.anonymousCtor
        "⟨"
        [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `c [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `c [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `acd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `c "." `support) "." `attach)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `c "." `support)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum
      "∑"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
      " in "
      (Term.proj (Term.proj `c "." `support) "." `attach)
      ", "
      («term_*_»
       (Term.app
        `acd
        [(Term.paren "(" (Term.app `c [`i]) ")")
         (Term.paren
          "("
          (Term.app
           (Term.proj `Finset.mem_image "." `mpr)
           [(Term.anonymousCtor
             "⟨"
             [`i "," (Term.anonymousCtor "⟨" [(Term.proj `i "." (fieldIdx "2")) "," `rfl] "⟩")]
             "⟩")])
          ")")])
       "*"
       (Term.proj (Term.proj (Term.proj `i "." (fieldIdx "1")) "." (fieldIdx "2")) "." `some)))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» («term_^_» `f "^" `N) " • " (Term.proj `z "." `val))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `z "." `val)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 80, (some 80, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `y)
       («binderTerm∈_» "∈" (Term.app (Term.proj (Term.proj `c "." `support) "." `image) [`c]))
       ","
       `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `c "." `support) "." `image) [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `c "." `support) "." `image)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `c "." `support)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Finsupp.Defs.«term_→₀_»
       (Set.Data.Set.Image.term_''_
        (Term.app `algebraMap [`A (Term.app `Away [`f])])
        " '' "
        (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
       " →₀ "
       (Term.app `Away [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Set.Data.Set.Image.term_''_
       (Term.app `algebraMap [`A (Term.app `Away [`f])])
       " '' "
       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `algebraMap [`A (Term.app `Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 80, (some 81, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `z "∈" (Term.app `carrier [`𝒜 `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier [`𝒜 `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  MemCarrier.clear_denominator
  [ DecidableEq Away f ] { z : A⁰_ f } ( hz : z ∈ carrier 𝒜 x )
    :
      ∃
        ( c : algebraMap A Away f '' x . 1 . asHomogeneousIdeal →₀ Away f )
          ( N : ℕ )
          ( acd : ∀ y ∈ c . support . image c , A )
        ,
        f ^ N • z . val
          =
          algebraMap
            A
              Away f
              ∑
                i
                in
                c . support . attach
                ,
                acd c i Finset.mem_image . mpr ⟨ i , ⟨ i . 2 , rfl ⟩ ⟩ * i . 1 . 2 . some
  := MemCarrier.clear_denominator' x <| mem_carrier_iff 𝒜 x z . mpr hz
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier.clear_denominator AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.MemCarrier.clear_denominator

theorem disjoint : Disjoint (x.1.asHomogeneousIdeal.toIdeal : Set A) (Submonoid.powers f : Set A) :=
  by
  by_contra rid
  rw [Set.not_disjoint_iff] at rid
  choose g hg using rid
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg
  by_cases k_ineq : 0 < k
  · erw [x.1.IsPrime.pow_mem_iff_mem _ k_ineq] at hg1
    exact x.2 hg1
  · erw [show k = 0 by linarith, pow_zero, ← Ideal.eq_top_iff_one] at hg1
    apply x.1.IsPrime.1
    exact hg1
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.disjoint AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.disjoint

theorem carrier_ne_top : carrier 𝒜 x ≠ ⊤ :=
  by
  have eq_top := Disjoint x
  classical
    contrapose! eq_top
    obtain ⟨c, N, acd, eq1⟩ :=
      mem_carrier.clear_denominator _ x ((Ideal.eq_top_iff_one _).mp eq_top)
    rw [Algebra.smul_def, HomogeneousLocalization.one_val, mul_one] at eq1
    change Localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1
    simp only [mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    erw [mul_one, mul_one] at eq1
    change f ^ _ * f ^ _ = _ * f ^ _ at eq1
    rw [Set.not_disjoint_iff_nonempty_inter]
    refine'
      ⟨f ^ N * f ^ M, eq1.symm ▸ mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _),
        ⟨N + M, by rw [pow_add]⟩⟩
    generalize_proofs h₁ h₂
    exact (Classical.choose_spec h₂).1
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier_ne_top AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier_ne_top

variable (f)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in\n`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toFun [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»
           "Proj.T| "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
          "Spec.T "
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app `carrier [`𝒜 `x])
         ","
         (Term.app `carrier_ne_top [`x])
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x1 `x2 `hx12]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.tacticClassical_
                "classical"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
                    [(Tactic.location
                      "at"
                      (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
                   []
                   (Tactic.tacticLet_
                    "let"
                    (Term.letDecl
                     (Term.letIdDecl
                      `J
                      []
                      []
                      ":="
                      (Term.app
                       `span
                       [(Set.Data.Set.Image.term_''_
                         (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
                         " '' "
                         `x.val.as_homogeneous_ideal)]))))
                   []
                   (Mathlib.Tactic.tacticSuffices_
                    "suffices"
                    [`h []]
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [`x `y]
                       [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
                       ","
                       (Term.arrow
                        («term_∈_» («term_*_» `x "*" `y) "∈" `J)
                        "→"
                        («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
                     []
                     (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
                   []
                   (Tactic.clear "clear" [`x1 `x2 `hx12])
                   []
                   (Tactic.intro "intro" [`x1 `x2 `hx12])
                   []
                   (Tactic.induction'
                    "induction'"
                    [(Tactic.casesTarget [] `x1)]
                    ["using" `Localization.induction_on]
                    ["with" [(Lean.binderIdent `data_x1)]]
                    [])
                   []
                   (Tactic.induction'
                    "induction'"
                    [(Tactic.casesTarget [] `x2)]
                    ["using" `Localization.induction_on]
                    ["with" [(Lean.binderIdent `data_x2)]]
                    [])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `a1)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.tuple
                                   "⟨"
                                   [(Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `n1)])
                                     [])
                                    ","
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                     [])]
                                   "⟩")])
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
                                 [(Std.Tactic.RCases.rcasesPat.one `a2)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.tuple
                                   "⟨"
                                   [(Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `n2)])
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
                         "⟩")])
                      [])])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                           [])]
                         "⟩")])
                      [])])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Tactic.change
                    "change"
                    («term_=_»
                     («term_*_»
                      (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                      "*"
                      («term_*_»
                       (Term.app `mk [(Term.hole "_") (Term.hole "_")])
                       "*"
                       (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
                     "="
                     (Term.app
                      `mk
                      [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                        "∑"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                        ", "
                        (Term.hole "_"))
                       (Term.hole "_")]))
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Localization.mk_mul)
                      ","
                      (Tactic.simpLemma [] [] `one_mul)]
                     "]"]
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `mk_eq_mk')
                      ","
                      (Tactic.simpLemma [] [] `IsLocalization.eq)]
                     "]"]
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget [] `eq1)]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.tuple
                                   "⟨"
                                   [(Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `M)])
                                     [])
                                    ","
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                     [])]
                                   "⟩")])
                                [])]
                              "⟩")])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                           [])]
                         "⟩")])
                      [])])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Tactic.change
                    "change"
                    («term_=_»
                     («term_*_»
                      («term_*_» (Term.hole "_") "*" (Term.hole "_"))
                      "*"
                      («term_^_» `f "^" (Term.hole "_")))
                     "="
                     («term_*_»
                      («term_*_»
                       (Term.hole "_")
                       "*"
                       («term_*_»
                        («term_^_» `f "^" (Term.hole "_"))
                        "*"
                        («term_^_» `f "^" (Term.hole "_"))))
                      "*"
                      («term_^_» `f "^" (Term.hole "_"))))
                    [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app
                       (Term.proj
                        (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                        "."
                        `mem_or_mem)
                       [(Term.show
                         "show"
                         («term_∈_»
                          («term_*_»
                           («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
                           "*"
                           («term_^_» `f "^" `M))
                          "∈"
                          (Term.hole "_"))
                         (Term.fromTerm "from" (Term.hole "_")))]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.paren
                         "("
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `h1)
                            "|"
                            (Std.Tactic.RCases.rcasesPat.one `rid2)])
                          [])
                         ")")])
                      [])])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app
                       (Term.proj
                        (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                        "."
                        `mem_or_mem)
                       [`h1]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.paren
                         "("
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `h1)
                            "|"
                            (Std.Tactic.RCases.rcasesPat.one `rid1)])
                          [])
                         ")")])
                      [])])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app
                       (Term.proj
                        (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                        "."
                        `mem_or_mem)
                       [`h1]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.paren
                         "("
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `h1)
                            "|"
                            (Std.Tactic.RCases.rcasesPat.one `h2)])
                          [])
                         ")")])
                      [])])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Mathlib.Tactic.tacticLeft "left")
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
                         (Term.show
                          "show"
                          («term_=_»
                           (Term.typeAscription
                            "("
                            (Term.app
                             `mk
                             [`a1
                              (Term.anonymousCtor
                               "⟨"
                               [(«term_^_» `f "^" `n1) "," (Term.hole "_")]
                               "⟩")])
                            ":"
                            [(Term.app `away [`f])]
                            ")")
                           "="
                           («term_*_»
                            (Term.app `mk [`a1 (num "1")])
                            "*"
                            (Term.app
                             `mk
                             [(num "1")
                              (Term.anonymousCtor
                               "⟨"
                               [(«term_^_» `f "^" `n1)
                                ","
                                (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                               "⟩")])))
                          (Term.byTactic'
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `Localization.mk_mul)
                                 ","
                                 (Tactic.rwRule [] `mul_one)
                                 ","
                                 (Tactic.rwRule [] `one_mul)]
                                "]")
                               [])])))))]
                       "]"]
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `Ideal.mul_mem_right
                       [(Term.hole "_")
                        (Term.hole "_")
                        (Term.app
                         `Ideal.subset_span
                         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Mathlib.Tactic.tacticRight "right")
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
                         (Term.show
                          "show"
                          («term_=_»
                           (Term.typeAscription
                            "("
                            (Term.app
                             `mk
                             [`a2
                              (Term.anonymousCtor
                               "⟨"
                               [(«term_^_» `f "^" `n2) "," (Term.hole "_")]
                               "⟩")])
                            ":"
                            [(Term.app `away [`f])]
                            ")")
                           "="
                           («term_*_»
                            (Term.app `mk [`a2 (num "1")])
                            "*"
                            (Term.app
                             `mk
                             [(num "1")
                              (Term.anonymousCtor
                               "⟨"
                               [(«term_^_» `f "^" `n2)
                                ","
                                (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                               "⟩")])))
                          (Term.byTactic'
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `Localization.mk_mul)
                                 ","
                                 (Tactic.rwRule [] `mul_one)
                                 ","
                                 (Tactic.rwRule [] `one_mul)]
                                "]")
                               [])])))))]
                       "]"]
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `Ideal.mul_mem_right
                       [(Term.hole "_")
                        (Term.hole "_")
                        (Term.app
                         `Ideal.subset_span
                         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.exact
                      "exact"
                      (Term.app
                       `False.elim
                       [(Term.app
                         (Term.proj `x "." (fieldIdx "2"))
                         [(Term.app
                           (Term.proj
                            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                            "."
                            `mem_of_pow_mem)
                           [`N `rid1])])]))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.exact
                      "exact"
                      (Term.app
                       `False.elim
                       [(Term.app
                         (Term.proj `x "." (fieldIdx "2"))
                         [(Term.app
                           (Term.proj
                            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                            "."
                            `mem_of_pow_mem)
                           [`M `rid2])])]))])
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
                         (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                        ","
                        (Tactic.rwRule [] `eq1)]
                       "]")
                      [])
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       `mul_mem_right
                       [(Term.hole "_")
                        (Term.hole "_")
                        (Term.app
                         `mul_mem_right
                         [(Term.hole "_")
                          (Term.hole "_")
                          (Term.app
                           `sum_mem
                           [(Term.hole "_")
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`i `hi]
                              []
                              "=>"
                              (Term.app
                               `mul_mem_left
                               [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                     []
                     (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                      "generalize_proofs"
                      [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.proj
                       (Term.app `Classical.choose_spec [`h₂])
                       "."
                       (fieldIdx "1")))])])))])))))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `carrier [`𝒜 `x])
        ","
        (Term.app `carrier_ne_top [`x])
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x1 `x2 `hx12]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Mathlib.Tactic.tacticClassical_
               "classical"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
                   [(Tactic.location
                     "at"
                     (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `J
                     []
                     []
                     ":="
                     (Term.app
                      `span
                      [(Set.Data.Set.Image.term_''_
                        (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
                        " '' "
                        `x.val.as_homogeneous_ideal)]))))
                  []
                  (Mathlib.Tactic.tacticSuffices_
                   "suffices"
                   [`h []]
                   [(Term.typeSpec
                     ":"
                     (Term.forall
                      "∀"
                      [`x `y]
                      [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
                      ","
                      (Term.arrow
                       («term_∈_» («term_*_» `x "*" `y) "∈" `J)
                       "→"
                       («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
                    []
                    (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
                  []
                  (Tactic.clear "clear" [`x1 `x2 `hx12])
                  []
                  (Tactic.intro "intro" [`x1 `x2 `hx12])
                  []
                  (Tactic.induction'
                   "induction'"
                   [(Tactic.casesTarget [] `x1)]
                   ["using" `Localization.induction_on]
                   ["with" [(Lean.binderIdent `data_x1)]]
                   [])
                  []
                  (Tactic.induction'
                   "induction'"
                   [(Tactic.casesTarget [] `x2)]
                   ["using" `Localization.induction_on]
                   ["with" [(Lean.binderIdent `data_x2)]]
                   [])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `a1)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.tuple
                                  "⟨"
                                  [(Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `n1)])
                                    [])
                                   ","
                                   (Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                    [])]
                                  "⟩")])
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
                                [(Std.Tactic.RCases.rcasesPat.one `a2)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.tuple
                                  "⟨"
                                  [(Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `n2)])
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
                        "⟩")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Tactic.change
                   "change"
                   («term_=_»
                    («term_*_»
                     (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                     "*"
                     («term_*_»
                      (Term.app `mk [(Term.hole "_") (Term.hole "_")])
                      "*"
                      (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
                    "="
                    (Term.app
                     `mk
                     [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                       "∑"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                       ", "
                       (Term.hole "_"))
                      (Term.hole "_")]))
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Localization.mk_mul)
                     ","
                     (Tactic.simpLemma [] [] `one_mul)]
                    "]"]
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `mk_eq_mk')
                     ","
                     (Tactic.simpLemma [] [] `IsLocalization.eq)]
                    "]"]
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `eq1)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.tuple
                                  "⟨"
                                  [(Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `M)])
                                    [])
                                   ","
                                   (Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                    [])]
                                  "⟩")])
                               [])]
                             "⟩")])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Tactic.change
                   "change"
                   («term_=_»
                    («term_*_»
                     («term_*_» (Term.hole "_") "*" (Term.hole "_"))
                     "*"
                     («term_^_» `f "^" (Term.hole "_")))
                    "="
                    («term_*_»
                     («term_*_»
                      (Term.hole "_")
                      "*"
                      («term_*_»
                       («term_^_» `f "^" (Term.hole "_"))
                       "*"
                       («term_^_» `f "^" (Term.hole "_"))))
                     "*"
                     («term_^_» `f "^" (Term.hole "_"))))
                   [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app
                      (Term.proj
                       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_or_mem)
                      [(Term.show
                        "show"
                        («term_∈_»
                         («term_*_»
                          («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
                          "*"
                          («term_^_» `f "^" `M))
                         "∈"
                         (Term.hole "_"))
                        (Term.fromTerm "from" (Term.hole "_")))]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.paren
                        "("
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `h1)
                           "|"
                           (Std.Tactic.RCases.rcasesPat.one `rid2)])
                         [])
                        ")")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app
                      (Term.proj
                       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_or_mem)
                      [`h1]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.paren
                        "("
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `h1)
                           "|"
                           (Std.Tactic.RCases.rcasesPat.one `rid1)])
                         [])
                        ")")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app
                      (Term.proj
                       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_or_mem)
                      [`h1]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.paren
                        "("
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `h1)
                           "|"
                           (Std.Tactic.RCases.rcasesPat.one `h2)])
                         [])
                        ")")])
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Mathlib.Tactic.tacticLeft "left")
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
                        (Term.show
                         "show"
                         («term_=_»
                          (Term.typeAscription
                           "("
                           (Term.app
                            `mk
                            [`a1
                             (Term.anonymousCtor
                              "⟨"
                              [(«term_^_» `f "^" `n1) "," (Term.hole "_")]
                              "⟩")])
                           ":"
                           [(Term.app `away [`f])]
                           ")")
                          "="
                          («term_*_»
                           (Term.app `mk [`a1 (num "1")])
                           "*"
                           (Term.app
                            `mk
                            [(num "1")
                             (Term.anonymousCtor
                              "⟨"
                              [(«term_^_» `f "^" `n1)
                               ","
                               (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                              "⟩")])))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] `Localization.mk_mul)
                                ","
                                (Tactic.rwRule [] `mul_one)
                                ","
                                (Tactic.rwRule [] `one_mul)]
                               "]")
                              [])])))))]
                      "]"]
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `Ideal.mul_mem_right
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app
                        `Ideal.subset_span
                        [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Mathlib.Tactic.tacticRight "right")
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
                        (Term.show
                         "show"
                         («term_=_»
                          (Term.typeAscription
                           "("
                           (Term.app
                            `mk
                            [`a2
                             (Term.anonymousCtor
                              "⟨"
                              [(«term_^_» `f "^" `n2) "," (Term.hole "_")]
                              "⟩")])
                           ":"
                           [(Term.app `away [`f])]
                           ")")
                          "="
                          («term_*_»
                           (Term.app `mk [`a2 (num "1")])
                           "*"
                           (Term.app
                            `mk
                            [(num "1")
                             (Term.anonymousCtor
                              "⟨"
                              [(«term_^_» `f "^" `n2)
                               ","
                               (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                              "⟩")])))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] `Localization.mk_mul)
                                ","
                                (Tactic.rwRule [] `mul_one)
                                ","
                                (Tactic.rwRule [] `one_mul)]
                               "]")
                              [])])))))]
                      "]"]
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `Ideal.mul_mem_right
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app
                        `Ideal.subset_span
                        [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `False.elim
                      [(Term.app
                        (Term.proj `x "." (fieldIdx "2"))
                        [(Term.app
                          (Term.proj
                           (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                           "."
                           `mem_of_pow_mem)
                          [`N `rid1])])]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `False.elim
                      [(Term.app
                        (Term.proj `x "." (fieldIdx "2"))
                        [(Term.app
                          (Term.proj
                           (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                           "."
                           `mem_of_pow_mem)
                          [`M `rid2])])]))])
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
                        (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                       ","
                       (Tactic.rwRule [] `eq1)]
                      "]")
                     [])
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `mul_mem_right
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app
                        `mul_mem_right
                        [(Term.hole "_")
                         (Term.hole "_")
                         (Term.app
                          `sum_mem
                          [(Term.hole "_")
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`i `hi]
                             []
                             "=>"
                             (Term.app
                              `mul_mem_left
                              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                    []
                    (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                     "generalize_proofs"
                     [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.proj
                      (Term.app `Classical.choose_spec [`h₂])
                      "."
                      (fieldIdx "1")))])])))])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x1 `x2 `hx12]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.tacticClassical_
             "classical"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
                 [(Tactic.location
                   "at"
                   (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
                []
                (Tactic.tacticLet_
                 "let"
                 (Term.letDecl
                  (Term.letIdDecl
                   `J
                   []
                   []
                   ":="
                   (Term.app
                    `span
                    [(Set.Data.Set.Image.term_''_
                      (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
                      " '' "
                      `x.val.as_homogeneous_ideal)]))))
                []
                (Mathlib.Tactic.tacticSuffices_
                 "suffices"
                 [`h []]
                 [(Term.typeSpec
                   ":"
                   (Term.forall
                    "∀"
                    [`x `y]
                    [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
                    ","
                    (Term.arrow
                     («term_∈_» («term_*_» `x "*" `y) "∈" `J)
                     "→"
                     («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
                  []
                  (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
                []
                (Tactic.clear "clear" [`x1 `x2 `hx12])
                []
                (Tactic.intro "intro" [`x1 `x2 `hx12])
                []
                (Tactic.induction'
                 "induction'"
                 [(Tactic.casesTarget [] `x1)]
                 ["using" `Localization.induction_on]
                 ["with" [(Lean.binderIdent `data_x1)]]
                 [])
                []
                (Tactic.induction'
                 "induction'"
                 [(Tactic.casesTarget [] `x2)]
                 ["using" `Localization.induction_on]
                 ["with" [(Lean.binderIdent `data_x2)]]
                 [])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `a1)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `n1)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                  [])]
                                "⟩")])
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
                              [(Std.Tactic.RCases.rcasesPat.one `a2)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `n2)])
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
                      "⟩")])
                   [])])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  («term_*_»
                   (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                   "*"
                   («term_*_»
                    (Term.app `mk [(Term.hole "_") (Term.hole "_")])
                    "*"
                    (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
                  "="
                  (Term.app
                   `mk
                   [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                     "∑"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                     ", "
                     (Term.hole "_"))
                    (Term.hole "_")]))
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Localization.mk_mul)
                   ","
                   (Tactic.simpLemma [] [] `one_mul)]
                  "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `mk_eq_mk')
                   ","
                   (Tactic.simpLemma [] [] `IsLocalization.eq)]
                  "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `eq1)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `M)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                  [])]
                                "⟩")])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  («term_*_»
                   («term_*_» (Term.hole "_") "*" (Term.hole "_"))
                   "*"
                   («term_^_» `f "^" (Term.hole "_")))
                  "="
                  («term_*_»
                   («term_*_»
                    (Term.hole "_")
                    "*"
                    («term_*_»
                     («term_^_» `f "^" (Term.hole "_"))
                     "*"
                     («term_^_» `f "^" (Term.hole "_"))))
                   "*"
                   («term_^_» `f "^" (Term.hole "_"))))
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                     "."
                     `mem_or_mem)
                    [(Term.show
                      "show"
                      («term_∈_»
                       («term_*_»
                        («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
                        "*"
                        («term_^_» `f "^" `M))
                       "∈"
                       (Term.hole "_"))
                      (Term.fromTerm "from" (Term.hole "_")))]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `h1)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `rid2)])
                       [])
                      ")")])
                   [])])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                     "."
                     `mem_or_mem)
                    [`h1]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `h1)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `rid1)])
                       [])
                      ")")])
                   [])])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                     "."
                     `mem_or_mem)
                    [`h1]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `h1)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `h2)])
                       [])
                      ")")])
                   [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Mathlib.Tactic.tacticLeft "left")
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
                      (Term.show
                       "show"
                       («term_=_»
                        (Term.typeAscription
                         "("
                         (Term.app
                          `mk
                          [`a1
                           (Term.anonymousCtor
                            "⟨"
                            [(«term_^_» `f "^" `n1) "," (Term.hole "_")]
                            "⟩")])
                         ":"
                         [(Term.app `away [`f])]
                         ")")
                        "="
                        («term_*_»
                         (Term.app `mk [`a1 (num "1")])
                         "*"
                         (Term.app
                          `mk
                          [(num "1")
                           (Term.anonymousCtor
                            "⟨"
                            [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                            "⟩")])))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `Localization.mk_mul)
                              ","
                              (Tactic.rwRule [] `mul_one)
                              ","
                              (Tactic.rwRule [] `one_mul)]
                             "]")
                            [])])))))]
                    "]"]
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Ideal.mul_mem_right
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `Ideal.subset_span
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Mathlib.Tactic.tacticRight "right")
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
                      (Term.show
                       "show"
                       («term_=_»
                        (Term.typeAscription
                         "("
                         (Term.app
                          `mk
                          [`a2
                           (Term.anonymousCtor
                            "⟨"
                            [(«term_^_» `f "^" `n2) "," (Term.hole "_")]
                            "⟩")])
                         ":"
                         [(Term.app `away [`f])]
                         ")")
                        "="
                        («term_*_»
                         (Term.app `mk [`a2 (num "1")])
                         "*"
                         (Term.app
                          `mk
                          [(num "1")
                           (Term.anonymousCtor
                            "⟨"
                            [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                            "⟩")])))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `Localization.mk_mul)
                              ","
                              (Tactic.rwRule [] `mul_one)
                              ","
                              (Tactic.rwRule [] `one_mul)]
                             "]")
                            [])])))))]
                    "]"]
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Ideal.mul_mem_right
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `Ideal.subset_span
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.app
                    `False.elim
                    [(Term.app
                      (Term.proj `x "." (fieldIdx "2"))
                      [(Term.app
                        (Term.proj
                         (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                         "."
                         `mem_of_pow_mem)
                        [`N `rid1])])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.app
                    `False.elim
                    [(Term.app
                      (Term.proj `x "." (fieldIdx "2"))
                      [(Term.app
                        (Term.proj
                         (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                         "."
                         `mem_of_pow_mem)
                        [`M `rid2])])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                     ","
                     (Tactic.rwRule [] `eq1)]
                    "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `mul_mem_right
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `mul_mem_right
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app
                        `sum_mem
                        [(Term.hole "_")
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`i `hi]
                           []
                           "=>"
                           (Term.app
                            `mul_mem_left
                            [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                  []
                  (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                   "generalize_proofs"
                   [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.proj
                    (Term.app `Classical.choose_spec [`h₂])
                    "."
                    (fieldIdx "1")))])])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
               [(Tactic.location
                 "at"
                 (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `J
                 []
                 []
                 ":="
                 (Term.app
                  `span
                  [(Set.Data.Set.Image.term_''_
                    (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
                    " '' "
                    `x.val.as_homogeneous_ideal)]))))
              []
              (Mathlib.Tactic.tacticSuffices_
               "suffices"
               [`h []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [`x `y]
                  [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
                  ","
                  (Term.arrow
                   («term_∈_» («term_*_» `x "*" `y) "∈" `J)
                   "→"
                   («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
                []
                (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
              []
              (Tactic.clear "clear" [`x1 `x2 `hx12])
              []
              (Tactic.intro "intro" [`x1 `x2 `hx12])
              []
              (Tactic.induction'
               "induction'"
               [(Tactic.casesTarget [] `x1)]
               ["using" `Localization.induction_on]
               ["with" [(Lean.binderIdent `data_x1)]]
               [])
              []
              (Tactic.induction'
               "induction'"
               [(Tactic.casesTarget [] `x2)]
               ["using" `Localization.induction_on]
               ["with" [(Lean.binderIdent `data_x2)]]
               [])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `n1)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                [])]
                              "⟩")])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a2)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `n2)])
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
                    "⟩")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Tactic.change
               "change"
               («term_=_»
                («term_*_»
                 (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                 "*"
                 («term_*_»
                  (Term.app `mk [(Term.hole "_") (Term.hole "_")])
                  "*"
                  (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
                "="
                (Term.app
                 `mk
                 [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                   ", "
                   (Term.hole "_"))
                  (Term.hole "_")]))
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Localization.mk_mul)
                 ","
                 (Tactic.simpLemma [] [] `one_mul)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `mk_eq_mk')
                 ","
                 (Tactic.simpLemma [] [] `IsLocalization.eq)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `eq1)]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `M)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                [])]
                              "⟩")])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Tactic.change
               "change"
               («term_=_»
                («term_*_»
                 («term_*_» (Term.hole "_") "*" (Term.hole "_"))
                 "*"
                 («term_^_» `f "^" (Term.hole "_")))
                "="
                («term_*_»
                 («term_*_»
                  (Term.hole "_")
                  "*"
                  («term_*_»
                   («term_^_» `f "^" (Term.hole "_"))
                   "*"
                   («term_^_» `f "^" (Term.hole "_"))))
                 "*"
                 («term_^_» `f "^" (Term.hole "_"))))
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_or_mem)
                  [(Term.show
                    "show"
                    («term_∈_»
                     («term_*_»
                      («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
                      "*"
                      («term_^_» `f "^" `M))
                     "∈"
                     (Term.hole "_"))
                    (Term.fromTerm "from" (Term.hole "_")))]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.paren
                    "("
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `h1)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.one `rid2)])
                     [])
                    ")")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_or_mem)
                  [`h1]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.paren
                    "("
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `h1)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.one `rid1)])
                     [])
                    ")")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_or_mem)
                  [`h1]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.paren
                    "("
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `h1)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.one `h2)])
                     [])
                    ")")])
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Mathlib.Tactic.tacticLeft "left")
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
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.typeAscription
                       "("
                       (Term.app
                        `mk
                        [`a1
                         (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
                       ":"
                       [(Term.app `away [`f])]
                       ")")
                      "="
                      («term_*_»
                       (Term.app `mk [`a1 (num "1")])
                       "*"
                       (Term.app
                        `mk
                        [(num "1")
                         (Term.anonymousCtor
                          "⟨"
                          [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                          "⟩")])))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `Localization.mk_mul)
                            ","
                            (Tactic.rwRule [] `mul_one)
                            ","
                            (Tactic.rwRule [] `one_mul)]
                           "]")
                          [])])))))]
                  "]"]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `Ideal.mul_mem_right
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app
                    `Ideal.subset_span
                    [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Mathlib.Tactic.tacticRight "right")
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
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.typeAscription
                       "("
                       (Term.app
                        `mk
                        [`a2
                         (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
                       ":"
                       [(Term.app `away [`f])]
                       ")")
                      "="
                      («term_*_»
                       (Term.app `mk [`a2 (num "1")])
                       "*"
                       (Term.app
                        `mk
                        [(num "1")
                         (Term.anonymousCtor
                          "⟨"
                          [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                          "⟩")])))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `Localization.mk_mul)
                            ","
                            (Tactic.rwRule [] `mul_one)
                            ","
                            (Tactic.rwRule [] `one_mul)]
                           "]")
                          [])])))))]
                  "]"]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `Ideal.mul_mem_right
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app
                    `Ideal.subset_span
                    [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.app
                  `False.elim
                  [(Term.app
                    (Term.proj `x "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj
                       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_of_pow_mem)
                      [`N `rid1])])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.app
                  `False.elim
                  [(Term.app
                    (Term.proj `x "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj
                       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_of_pow_mem)
                      [`M `rid2])])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                   ","
                   (Tactic.rwRule [] `eq1)]
                  "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `mul_mem_right
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app
                    `mul_mem_right
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `sum_mem
                      [(Term.hole "_")
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`i `hi]
                         []
                         "=>"
                         (Term.app
                          `mul_mem_left
                          [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                []
                (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                 "generalize_proofs"
                 [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `J
             []
             []
             ":="
             (Term.app
              `span
              [(Set.Data.Set.Image.term_''_
                (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
                " '' "
                `x.val.as_homogeneous_ideal)]))))
          []
          (Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`h []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`x `y]
              [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
              ","
              (Term.arrow
               («term_∈_» («term_*_» `x "*" `y) "∈" `J)
               "→"
               («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
            []
            (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
          []
          (Tactic.clear "clear" [`x1 `x2 `hx12])
          []
          (Tactic.intro "intro" [`x1 `x2 `hx12])
          []
          (Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `x1)]
           ["using" `Localization.induction_on]
           ["with" [(Lean.binderIdent `data_x1)]]
           [])
          []
          (Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `x2)]
           ["using" `Localization.induction_on]
           ["with" [(Lean.binderIdent `data_x2)]]
           [])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n1)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n2)])
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
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_*_»
             (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
             "*"
             («term_*_»
              (Term.app `mk [(Term.hole "_") (Term.hole "_")])
              "*"
              (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
            "="
            (Term.app
             `mk
             [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
               ", "
               (Term.hole "_"))
              (Term.hole "_")]))
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Localization.mk_mul) "," (Tactic.simpLemma [] [] `one_mul)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `mk_eq_mk') "," (Tactic.simpLemma [] [] `IsLocalization.eq)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `eq1)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
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
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `M)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_*_»
             («term_*_» (Term.hole "_") "*" (Term.hole "_"))
             "*"
             («term_^_» `f "^" (Term.hole "_")))
            "="
            («term_*_»
             («term_*_»
              (Term.hole "_")
              "*"
              («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_"))))
             "*"
             («term_^_» `f "^" (Term.hole "_"))))
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
              [(Term.show
                "show"
                («term_∈_»
                 («term_*_»
                  («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
                  "*"
                  («term_^_» `f "^" `M))
                 "∈"
                 (Term.hole "_"))
                (Term.fromTerm "from" (Term.hole "_")))]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `h1)
                   "|"
                   (Std.Tactic.RCases.rcasesPat.one `rid2)])
                 [])
                ")")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
              [`h1]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `h1)
                   "|"
                   (Std.Tactic.RCases.rcasesPat.one `rid1)])
                 [])
                ")")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
              [`h1]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `h1) "|" (Std.Tactic.RCases.rcasesPat.one `h2)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticLeft "left")
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
                (Term.show
                 "show"
                 («term_=_»
                  (Term.typeAscription
                   "("
                   (Term.app
                    `mk
                    [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
                   ":"
                   [(Term.app `away [`f])]
                   ")")
                  "="
                  («term_*_»
                   (Term.app `mk [`a1 (num "1")])
                   "*"
                   (Term.app
                    `mk
                    [(num "1")
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                      "⟩")])))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Localization.mk_mul)
                        ","
                        (Tactic.rwRule [] `mul_one)
                        ","
                        (Tactic.rwRule [] `one_mul)]
                       "]")
                      [])])))))]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `Ideal.mul_mem_right
              [(Term.hole "_")
               (Term.hole "_")
               (Term.app
                `Ideal.subset_span
                [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticRight "right")
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
                (Term.show
                 "show"
                 («term_=_»
                  (Term.typeAscription
                   "("
                   (Term.app
                    `mk
                    [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
                   ":"
                   [(Term.app `away [`f])]
                   ")")
                  "="
                  («term_*_»
                   (Term.app `mk [`a2 (num "1")])
                   "*"
                   (Term.app
                    `mk
                    [(num "1")
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                      "⟩")])))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Localization.mk_mul)
                        ","
                        (Tactic.rwRule [] `mul_one)
                        ","
                        (Tactic.rwRule [] `one_mul)]
                       "]")
                      [])])))))]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `Ideal.mul_mem_right
              [(Term.hole "_")
               (Term.hole "_")
               (Term.app
                `Ideal.subset_span
                [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `False.elim
              [(Term.app
                (Term.proj `x "." (fieldIdx "2"))
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_of_pow_mem)
                  [`N `rid1])])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `False.elim
              [(Term.app
                (Term.proj `x "." (fieldIdx "2"))
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_of_pow_mem)
                  [`M `rid2])])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
               ","
               (Tactic.rwRule [] `eq1)]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `mul_mem_right
              [(Term.hole "_")
               (Term.hole "_")
               (Term.app
                `mul_mem_right
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.app
                  `sum_mem
                  [(Term.hole "_")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `hi]
                     []
                     "=>"
                     (Term.app
                      `mul_mem_left
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
            []
            (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
             "generalize_proofs"
             [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
           ","
           (Tactic.rwRule [] `eq1)]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `mul_mem_right
            [(Term.hole "_")
             (Term.hole "_")
             (Term.app
              `sum_mem
              [(Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
        []
        (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
         "generalize_proofs"
         [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Classical.choose_spec [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Classical.choose_spec [`h₂])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
       "generalize_proofs"
       [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `mul_mem_right
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app
          `mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `sum_mem
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [`i `hi]
               []
               "=>"
               (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `mul_mem_right
         [(Term.hole "_")
          (Term.hole "_")
          (Term.app
           `sum_mem
           [(Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [`i `hi]
              []
              "=>"
              (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `sum_mem
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `hi]
            []
            "=>"
            (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sum_mem
       [(Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `hi]
          []
          "=>"
          (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `hi]
        []
        "=>"
        (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `mul_mem_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sum_mem
      [(Term.hole "_")
       (Term.fun
        "fun"
        (Term.basicFun
         [`i `hi]
         []
         "=>"
         (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_mem_right
      [(Term.hole "_")
       (Term.hole "_")
       (Term.paren
        "("
        (Term.app
         `sum_mem
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `hi]
            []
            "=>"
            (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
        ")")])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem_right
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
        [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
         ","
         (Tactic.rwRule [] `eq1)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `N) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
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
          `False.elim
          [(Term.app
            (Term.proj `x "." (fieldIdx "2"))
            [(Term.app
              (Term.proj
               (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
               "."
               `mem_of_pow_mem)
              [`M `rid2])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `False.elim
        [(Term.app
          (Term.proj `x "." (fieldIdx "2"))
          [(Term.app
            (Term.proj
             (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
             "."
             `mem_of_pow_mem)
            [`M `rid2])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `False.elim
       [(Term.app
         (Term.proj `x "." (fieldIdx "2"))
         [(Term.app
           (Term.proj
            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
            "."
            `mem_of_pow_mem)
           [`M `rid2])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `x "." (fieldIdx "2"))
       [(Term.app
         (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`M `rid2])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
       [`M `rid2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rid2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
      [`M `rid2])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `x "." (fieldIdx "2"))
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`M `rid2])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `False.elim
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
          `False.elim
          [(Term.app
            (Term.proj `x "." (fieldIdx "2"))
            [(Term.app
              (Term.proj
               (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
               "."
               `mem_of_pow_mem)
              [`N `rid1])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `False.elim
        [(Term.app
          (Term.proj `x "." (fieldIdx "2"))
          [(Term.app
            (Term.proj
             (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
             "."
             `mem_of_pow_mem)
            [`N `rid1])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `False.elim
       [(Term.app
         (Term.proj `x "." (fieldIdx "2"))
         [(Term.app
           (Term.proj
            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
            "."
            `mem_of_pow_mem)
           [`N `rid1])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `x "." (fieldIdx "2"))
       [(Term.app
         (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`N `rid1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
       [`N `rid1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rid1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
      [`N `rid1])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `x "." (fieldIdx "2"))
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`N `rid1])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `False.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticRight "right")
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
            (Term.show
             "show"
             («term_=_»
              (Term.typeAscription
               "("
               (Term.app
                `mk
                [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
               ":"
               [(Term.app `away [`f])]
               ")")
              "="
              («term_*_»
               (Term.app `mk [`a2 (num "1")])
               "*"
               (Term.app
                `mk
                [(num "1")
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                  "⟩")])))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Localization.mk_mul)
                    ","
                    (Tactic.rwRule [] `mul_one)
                    ","
                    (Tactic.rwRule [] `one_mul)]
                   "]")
                  [])])))))]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Ideal.mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `Ideal.subset_span
            [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Ideal.mul_mem_right
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app
          `Ideal.subset_span
          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `Ideal.subset_span
         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.subset_span
       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.subset_span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.subset_span [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h2 "," `rfl] "⟩")])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_right
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
          (Term.show
           "show"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app
              `mk
              [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
             ":"
             [(Term.app `away [`f])]
             ")")
            "="
            («term_*_»
             (Term.app `mk [`a2 (num "1")])
             "*"
             (Term.app
              `mk
              [(num "1")
               (Term.anonymousCtor
                "⟨"
                [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
                "⟩")])))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Localization.mk_mul)
                  ","
                  (Tactic.rwRule [] `mul_one)
                  ","
                  (Tactic.rwRule [] `one_mul)]
                 "]")
                [])])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app
          `mk
          [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
         ":"
         [(Term.app `away [`f])]
         ")")
        "="
        («term_*_»
         (Term.app `mk [`a2 (num "1")])
         "*"
         (Term.app
          `mk
          [(num "1")
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
            "⟩")])))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Localization.mk_mul)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [] `one_mul)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Localization.mk_mul)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app
         `mk
         [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
        ":"
        [(Term.app `away [`f])]
        ")")
       "="
       («term_*_»
        (Term.app `mk [`a2 (num "1")])
        "*"
        (Term.app
         `mk
         [(num "1")
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `mk [`a2 (num "1")])
       "*"
       (Term.app
        `mk
        [(num "1")
         (Term.anonymousCtor
          "⟨"
          [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk
       [(num "1")
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» `f "^" `n2) "," (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n2 "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `n2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n2
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `mk [`a2 (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `mk
        [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
       ":"
       [(Term.app `away [`f])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [`a2 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n2) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `n2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n2
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticRight "right")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticLeft "left")
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
            (Term.show
             "show"
             («term_=_»
              (Term.typeAscription
               "("
               (Term.app
                `mk
                [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
               ":"
               [(Term.app `away [`f])]
               ")")
              "="
              («term_*_»
               (Term.app `mk [`a1 (num "1")])
               "*"
               (Term.app
                `mk
                [(num "1")
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                  "⟩")])))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Localization.mk_mul)
                    ","
                    (Tactic.rwRule [] `mul_one)
                    ","
                    (Tactic.rwRule [] `one_mul)]
                   "]")
                  [])])))))]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Ideal.mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `Ideal.subset_span
            [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Ideal.mul_mem_right
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app
          `Ideal.subset_span
          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `Ideal.subset_span
         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.subset_span
       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.subset_span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.subset_span [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h1 "," `rfl] "⟩")])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_right
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
          (Term.show
           "show"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app
              `mk
              [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
             ":"
             [(Term.app `away [`f])]
             ")")
            "="
            («term_*_»
             (Term.app `mk [`a1 (num "1")])
             "*"
             (Term.app
              `mk
              [(num "1")
               (Term.anonymousCtor
                "⟨"
                [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
                "⟩")])))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Localization.mk_mul)
                  ","
                  (Tactic.rwRule [] `mul_one)
                  ","
                  (Tactic.rwRule [] `one_mul)]
                 "]")
                [])])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app
          `mk
          [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
         ":"
         [(Term.app `away [`f])]
         ")")
        "="
        («term_*_»
         (Term.app `mk [`a1 (num "1")])
         "*"
         (Term.app
          `mk
          [(num "1")
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
            "⟩")])))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Localization.mk_mul)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [] `one_mul)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Localization.mk_mul)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app
         `mk
         [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
        ":"
        [(Term.app `away [`f])]
        ")")
       "="
       («term_*_»
        (Term.app `mk [`a1 (num "1")])
        "*"
        (Term.app
         `mk
         [(num "1")
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `mk [`a1 (num "1")])
       "*"
       (Term.app
        `mk
        [(num "1")
         (Term.anonymousCtor
          "⟨"
          [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk
       [(num "1")
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» `f "^" `n1) "," (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n1 "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `n1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n1
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `mk [`a1 (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `mk
        [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
       ":"
       [(Term.app `away [`f])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [`a1 (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_^_» `f "^" `n1) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `n1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n1
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticLeft "left")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
          [`h1]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `h1) "|" (Std.Tactic.RCases.rcasesPat.one `h2)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
       [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
          [`h1]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `h1) "|" (Std.Tactic.RCases.rcasesPat.one `rid1)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
       [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
          [(Term.show
            "show"
            («term_∈_»
             («term_*_»
              («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
              "*"
              («term_^_» `f "^" `M))
             "∈"
             (Term.hole "_"))
            (Term.fromTerm "from" (Term.hole "_")))]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `h1) "|" (Std.Tactic.RCases.rcasesPat.one `rid2)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
       [(Term.show
         "show"
         («term_∈_»
          («term_*_»
           («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
           "*"
           («term_^_» `f "^" `M))
          "∈"
          (Term.hole "_"))
         (Term.fromTerm "from" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∈_»
        («term_*_»
         («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
         "*"
         («term_^_» `f "^" `M))
        "∈"
        (Term.hole "_"))
       (Term.fromTerm "from" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_»
       («term_*_»
        («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
        "*"
        («term_^_» `f "^" `M))
       "∈"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
       "*"
       («term_^_» `f "^" `M))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `M)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `a1 "*" `a2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a2
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      («term_∈_»
       («term_*_»
        («term_*_» («term_*_» `a1 "*" `a2) "*" («term_^_» `f "^" `N))
        "*"
        («term_^_» `f "^" `M))
       "∈"
       (Term.hole "_"))
      (Term.fromTerm "from" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_*_»
         («term_*_» (Term.hole "_") "*" (Term.hole "_"))
         "*"
         («term_^_» `f "^" (Term.hole "_")))
        "="
        («term_*_»
         («term_*_»
          (Term.hole "_")
          "*"
          («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_"))))
         "*"
         («term_^_» `f "^" (Term.hole "_"))))
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        («term_*_» (Term.hole "_") "*" (Term.hole "_"))
        "*"
        («term_^_» `f "^" (Term.hole "_")))
       "="
       («term_*_»
        («term_*_»
         (Term.hole "_")
         "*"
         («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_"))))
        "*"
        («term_^_» `f "^" (Term.hole "_"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        (Term.hole "_")
        "*"
        («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_"))))
       "*"
       («term_^_» `f "^" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       (Term.hole "_")
       "*"
       («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `f "^" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» («term_^_» `f "^" (Term.hole "_")) "*" («term_^_» `f "^" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_*_» (Term.hole "_") "*" (Term.hole "_"))
       "*"
       («term_^_» `f "^" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (Term.hole "_") "*" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submonoid.coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `eq1)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `M)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
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
        [(Tactic.simpLemma [] [] `mk_eq_mk') "," (Tactic.simpLemma [] [] `IsLocalization.eq)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsLocalization.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_eq_mk'
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
        [(Tactic.simpLemma [] [] `Localization.mk_mul) "," (Tactic.simpLemma [] [] `one_mul)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_*_»
         (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
         "*"
         («term_*_»
          (Term.app `mk [(Term.hole "_") (Term.hole "_")])
          "*"
          (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
        "="
        (Term.app
         `mk
         [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
           ", "
           (Term.hole "_"))
          (Term.hole "_")]))
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
        "*"
        («term_*_»
         (Term.app `mk [(Term.hole "_") (Term.hole "_")])
         "*"
         (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
       "="
       (Term.app
        `mk
        [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
          ", "
          (Term.hole "_"))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk
       [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
         ", "
         (Term.hole "_"))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
       ", "
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
      ", "
      (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
       "*"
       («term_*_»
        (Term.app `mk [(Term.hole "_") (Term.hole "_")])
        "*"
        (Term.app `mk [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `mk [(Term.hole "_") (Term.hole "_")])
       "*"
       (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [(Term.hole "_") (Term.hole "_")])
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
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `mk [(Term.hole "_") (Term.hole "_")])
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
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.app `mk [(Term.hole "_") (Term.hole "_")])
      "*"
      (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `N) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `Algebra.smul_def)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator' [`x `hx12]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_carrier.clear_denominator' [`x `hx12])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_carrier.clear_denominator'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `data_x1) "," (Tactic.casesTarget [] `data_x2)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `data_x2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `data_x1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `x2)]
       ["using" `Localization.induction_on]
       ["with" [(Lean.binderIdent `data_x2)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `x1)]
       ["using" `Localization.induction_on]
       ["with" [(Lean.binderIdent `data_x1)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x1 `x2 `hx12])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`x1 `x2 `hx12])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
        []
        (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `h [`x1.val `x2.val `hx12]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`x1.val `x2.val `hx12])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x2.val
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x1.val
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.mul_val)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx12] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HomogeneousLocalization.mul_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`h []]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`x `y]
          [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
          ","
          (Term.arrow
           («term_∈_» («term_*_» `x "*" `y) "∈" `J)
           "→"
           («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       [(Term.typeSpec ":" (Term.app `Localization.Away [`f]))]
       ","
       (Term.arrow
        («term_∈_» («term_*_» `x "*" `y) "∈" `J)
        "→"
        («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∈_» («term_*_» `x "*" `y) "∈" `J)
       "→"
       («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» («term_∈_» `x "∈" `J) "∨" («term_∈_» `y "∈" `J))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `y "∈" `J)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_∈_» `x "∈" `J)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_∈_» («term_*_» `x "*" `y) "∈" `J)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `J
         []
         []
         ":="
         (Term.app
          `span
          [(Set.Data.Set.Image.term_''_
            (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
            " '' "
            `x.val.as_homogeneous_ideal)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `span
       [(Set.Data.Set.Image.term_''_
         (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
         " '' "
         `x.val.as_homogeneous_ideal)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
       " '' "
       `x.val.as_homogeneous_ideal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.val.as_homogeneous_ideal
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Init.Coe.«term⇑_» "⇑" (Term.app `algebraMap [`A (Term.app `away [`f])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`A (Term.app `away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `algebraMap [`A (Term.paren "(" (Term.app `away [`f]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1023, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Init.Coe.«term⇑_»
       "⇑"
       (Term.paren "(" (Term.app `algebraMap [`A (Term.paren "(" (Term.app `away [`f]) ")")]) ")"))
      " '' "
      `x.val.as_homogeneous_ideal)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `span
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
       ["[" [(Tactic.simpLemma [] [] `mem_carrier_iff)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`hx12] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_carrier_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx12
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier_ne_top [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier [`𝒜 `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
       "Spec.T "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termSpec.T_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2382'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
    `Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
    -/
  def
    toFun
    ( x : Proj.T| pbo f ) : Spec.T A⁰_ f
    :=
      ⟨
        carrier 𝒜 x
          ,
          carrier_ne_top x
          ,
          fun
            x1 x2 hx12
              =>
              by
                classical
                  simp only [ mem_carrier_iff ] at hx12 ⊢
                    let J := span ⇑ algebraMap A away f '' x.val.as_homogeneous_ideal
                    suffices h : ∀ x y : Localization.Away f , x * y ∈ J → x ∈ J ∨ y ∈ J
                    · rw [ HomogeneousLocalization.mul_val ] at hx12 exact h x1.val x2.val hx12
                    clear x1 x2 hx12
                    intro x1 x2 hx12
                    induction' x1 using Localization.induction_on with data_x1
                    induction' x2 using Localization.induction_on with data_x2
                    rcases
                      data_x1 , data_x2
                      with ⟨ ⟨ a1 , _ , ⟨ n1 , rfl ⟩ ⟩ , ⟨ a2 , _ , ⟨ n2 , rfl ⟩ ⟩ ⟩
                    rcases mem_carrier.clear_denominator' x hx12 with ⟨ c , N , acd , eq1 ⟩
                    simp only [ Algebra.smul_def ] at eq1
                    change Localization.mk f ^ N 1 * mk _ _ * mk _ _ = mk ∑ _ , _ _ at eq1
                    simp only [ Localization.mk_mul , one_mul ] at eq1
                    simp only [ mk_eq_mk' , IsLocalization.eq ] at eq1
                    rcases eq1 with ⟨ ⟨ _ , ⟨ M , rfl ⟩ ⟩ , eq1 ⟩
                    rw [ Submonoid.coe_one , mul_one ] at eq1
                    change _ * _ * f ^ _ = _ * f ^ _ * f ^ _ * f ^ _ at eq1
                    rcases
                      x . 1 . IsPrime . mem_or_mem show a1 * a2 * f ^ N * f ^ M ∈ _ from _
                      with ( h1 | rid2 )
                    rcases x . 1 . IsPrime . mem_or_mem h1 with ( h1 | rid1 )
                    rcases x . 1 . IsPrime . mem_or_mem h1 with ( h1 | h2 )
                    ·
                      left
                        simp
                          only
                          [
                            show
                              ( mk a1 ⟨ f ^ n1 , _ ⟩ : away f )
                                =
                                mk a1 1 * mk 1 ⟨ f ^ n1 , ⟨ n1 , rfl ⟩ ⟩
                              by rw [ Localization.mk_mul , mul_one , one_mul ]
                            ]
                        exact Ideal.mul_mem_right _ _ Ideal.subset_span ⟨ _ , h1 , rfl ⟩
                    ·
                      right
                        simp
                          only
                          [
                            show
                              ( mk a2 ⟨ f ^ n2 , _ ⟩ : away f )
                                =
                                mk a2 1 * mk 1 ⟨ f ^ n2 , ⟨ n2 , rfl ⟩ ⟩
                              by rw [ Localization.mk_mul , mul_one , one_mul ]
                            ]
                        exact Ideal.mul_mem_right _ _ Ideal.subset_span ⟨ _ , h2 , rfl ⟩
                    · exact False.elim x . 2 x . 1 . IsPrime . mem_of_pow_mem N rid1
                    · exact False.elim x . 2 x . 1 . IsPrime . mem_of_pow_mem M rid2
                    ·
                      rw [ mul_comm _ f ^ N , eq1 ]
                        refine'
                          mul_mem_right
                            _ _ mul_mem_right _ _ sum_mem _ fun i hi => mul_mem_left _ _ _
                        generalize_proofs h₁ h₂
                        exact Classical.choose_spec h₂ . 1
        ⟩
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.toFun

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `preimage_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" `A] [] ")")
        (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder "(" [`a_mem] [":" («term_∈_» `a "∈" (Term.app `𝒜 [`k]))] [] ")")
        (Term.explicitBinder "(" [`b_mem1] [":" («term_∈_» `b "∈" (Term.app `𝒜 [`k]))] [] ")")
        (Term.explicitBinder
         "("
         [`b_mem2]
         [":" («term_∈_» `b "∈" (Term.app `Submonoid.powers [`f]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.app `toFun [`𝒜 `f])
          " ⁻¹' "
          (Term.typeAscription
           "("
           (Term.app
            (Term.explicit "@" `PrimeSpectrum.basicOpen)
            [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
             (Term.hole "_")
             (Term.app
              `Quotient.mk'
              [(Term.anonymousCtor
                "⟨"
                [`k
                 ","
                 (Term.anonymousCtor "⟨" [`a "," `a_mem] "⟩")
                 ","
                 (Term.anonymousCtor "⟨" [`b "," `b_mem1] "⟩")
                 ","
                 `b_mem2]
                "⟩")])])
           ":"
           [(Term.app
             `Set
             [(Term.app `PrimeSpectrum [(Term.app `HomogeneousLocalization.Away [`𝒜 `f])])])]
           ")"))
         "="
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
          "|"
          («term_∈_»
           (Term.proj `x "." (fieldIdx "1"))
           "∈"
           (Order.Basic.«term_⊓_»
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
            " ⊓ "
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)))
          "}"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.tacticExt1___
                "ext1"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.constructor "constructor")
                "<;>"
                (Tactic.intro "intro" [`hy]))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")]
                   "⟩"))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Set.mem_preimage)
                    ","
                    (Tactic.rwRule [] `opens.mem_coe)
                    ","
                    (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)]
                   "]")
                  [])
                 []
                 (Tactic.intro "intro" [`a_mem_y])
                 []
                 (Tactic.apply "apply" `hy)
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `to_fun)
                    ","
                    (Tactic.rwRule [] `mem_carrier_iff)
                    ","
                    (Tactic.rwRule [] `HomogeneousLocalization.val_mk')
                    ","
                    (Tactic.rwRule [] `Subtype.coe_mk)]
                   "]")
                  [])
                 []
                 (Tactic.dsimp "dsimp" [] [] [] [] [])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `b_mem2)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                         [])]
                       "⟩")])
                    [])])
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
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.typeAscription
                        "("
                        (Term.app
                         `mk
                         [`a
                          (Term.anonymousCtor
                           "⟨"
                           [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")]
                           "⟩")])
                        ":"
                        [(Term.app `away [`f])]
                        ")")
                       "="
                       («term_*_»
                        (Term.app
                         `mk
                         [(num "1")
                          (Term.anonymousCtor
                           "⟨"
                           [(«term_^_» `f "^" `k)
                            ","
                            (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
                           "⟩")])
                        "*"
                        (Term.app `mk [`a (num "1")])))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `mk_mul)
                             ","
                             (Tactic.rwRule [] `one_mul)
                             ","
                             (Tactic.rwRule [] `mul_one)]
                            "]")
                           [])
                          []
                          (Tactic.congr "congr" [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]")
                           [])])))))]
                   "]"]
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Ideal.mul_mem_left
                   [(Term.hole "_")
                    (Term.hole "_")
                    (Term.app
                     `Ideal.subset_span
                     [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.change
                  "change"
                  («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
                  [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `hy)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Set.mem_preimage)
                    ","
                    (Tactic.rwRule [] `to_fun)
                    ","
                    (Tactic.rwRule [] `opens.mem_coe)
                    ","
                    (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
                   "]")
                  [])
                 []
                 (Tactic.intro "intro" [`rid])
                 []
                 (Tactic.dsimp
                  "dsimp"
                  []
                  []
                  []
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`rid] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Algebra.smul_def)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Tactic.change
                  "change"
                  («term_=_»
                   («term_*_»
                    (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                    "*"
                    (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
                   "="
                   (Term.app
                    `mk
                    [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                      "∑"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                      ", "
                      (Term.hole "_"))
                     (Term.hole "_")]))
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mk_mul)
                    ","
                    (Tactic.rwRule [] `one_mul)
                    ","
                    (Tactic.rwRule [] `mk_eq_mk')
                    ","
                    (Tactic.rwRule [] `IsLocalization.eq)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `eq1)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.tuple
                                 "⟨"
                                 [(Std.Tactic.RCases.rcasesPatLo
                                   (Std.Tactic.RCases.rcasesPatMed
                                    [(Std.Tactic.RCases.rcasesPat.one `M)])
                                   [])
                                  ","
                                  (Std.Tactic.RCases.rcasesPatLo
                                   (Std.Tactic.RCases.rcasesPatMed
                                    [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                   [])]
                                 "⟩")])
                              [])]
                            "⟩")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     (Term.proj
                      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                      "."
                      `mem_or_mem)
                     [(Term.show
                       "show"
                       («term_∈_»
                        («term_*_»
                         («term_*_» `a "*" («term_^_» `f "^" `N))
                         "*"
                         («term_^_» `f "^" `M))
                        "∈"
                        (Term.hole "_"))
                       (Term.fromTerm "from" (Term.hole "_")))]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.paren
                       "("
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `H1)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `H3)])
                        [])
                       ")")])
                    [])])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     (Term.proj
                      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                      "."
                      `mem_or_mem)
                     [`H1]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.paren
                       "("
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `H1)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `H2)])
                        [])
                       ")")])
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `hy2 [`H1]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj `y "." (fieldIdx "2"))
                     [(Term.app
                       (Term.proj
                        (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                        "."
                        `mem_of_pow_mem)
                       [`N `H2])]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj `y "." (fieldIdx "2"))
                     [(Term.app
                       (Term.proj
                        (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                        "."
                        `mem_of_pow_mem)
                       [`M `H3])]))])
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
                       (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                      ","
                      (Tactic.rwRule [] `eq1)]
                     "]")
                    [])
                   []
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `mul_mem_right
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.app
                       `mul_mem_right
                       [(Term.hole "_")
                        (Term.hole "_")
                        (Term.app
                         `sum_mem
                         [(Term.hole "_")
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`i `hi]
                            []
                            "=>"
                            (Term.app
                             `mul_mem_left
                             [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                   []
                   (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                    "generalize_proofs"
                    [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.proj
                     (Term.app `Classical.choose_spec [`h₂])
                     "."
                     (fieldIdx "1")))])])])))])))
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
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Ext.tacticExt1___
               "ext1"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
              []
              (Tactic.«tactic_<;>_»
               (Tactic.constructor "constructor")
               "<;>"
               (Tactic.intro "intro" [`hy]))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")]
                  "⟩"))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Set.mem_preimage)
                   ","
                   (Tactic.rwRule [] `opens.mem_coe)
                   ","
                   (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)]
                  "]")
                 [])
                []
                (Tactic.intro "intro" [`a_mem_y])
                []
                (Tactic.apply "apply" `hy)
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `to_fun)
                   ","
                   (Tactic.rwRule [] `mem_carrier_iff)
                   ","
                   (Tactic.rwRule [] `HomogeneousLocalization.val_mk')
                   ","
                   (Tactic.rwRule [] `Subtype.coe_mk)]
                  "]")
                 [])
                []
                (Tactic.dsimp "dsimp" [] [] [] [] [])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `b_mem2)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                        [])]
                      "⟩")])
                   [])])
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
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.typeAscription
                       "("
                       (Term.app
                        `mk
                        [`a
                         (Term.anonymousCtor
                          "⟨"
                          [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")]
                          "⟩")])
                       ":"
                       [(Term.app `away [`f])]
                       ")")
                      "="
                      («term_*_»
                       (Term.app
                        `mk
                        [(num "1")
                         (Term.anonymousCtor
                          "⟨"
                          [(«term_^_» `f "^" `k)
                           ","
                           (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
                          "⟩")])
                       "*"
                       (Term.app `mk [`a (num "1")])))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `mk_mul)
                            ","
                            (Tactic.rwRule [] `one_mul)
                            ","
                            (Tactic.rwRule [] `mul_one)]
                           "]")
                          [])
                         []
                         (Tactic.congr "congr" [])
                         []
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]")
                          [])])))))]
                  "]"]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `Ideal.mul_mem_left
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app
                    `Ideal.subset_span
                    [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.change
                 "change"
                 («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
                 [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `hy)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Set.mem_preimage)
                   ","
                   (Tactic.rwRule [] `to_fun)
                   ","
                   (Tactic.rwRule [] `opens.mem_coe)
                   ","
                   (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
                  "]")
                 [])
                []
                (Tactic.intro "intro" [`rid])
                []
                (Tactic.dsimp
                 "dsimp"
                 []
                 []
                 []
                 []
                 [(Tactic.location "at" (Tactic.locationHyp [`rid] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Algebra.smul_def)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  («term_*_»
                   (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
                   "*"
                   (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
                  "="
                  (Term.app
                   `mk
                   [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                     "∑"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                     ", "
                     (Term.hole "_"))
                    (Term.hole "_")]))
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `mk_mul)
                   ","
                   (Tactic.rwRule [] `one_mul)
                   ","
                   (Tactic.rwRule [] `mk_eq_mk')
                   ","
                   (Tactic.rwRule [] `IsLocalization.eq)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `eq1)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `M)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                  [])]
                                "⟩")])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                     "."
                     `mem_or_mem)
                    [(Term.show
                      "show"
                      («term_∈_»
                       («term_*_»
                        («term_*_» `a "*" («term_^_» `f "^" `N))
                        "*"
                        («term_^_» `f "^" `M))
                       "∈"
                       (Term.hole "_"))
                      (Term.fromTerm "from" (Term.hole "_")))]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `H1)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `H3)])
                       [])
                      ")")])
                   [])])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                     "."
                     `mem_or_mem)
                    [`H1]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `H1)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `H2)])
                       [])
                      ")")])
                   [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact "exact" (Term.app `hy2 [`H1]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj `y "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj
                       (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_of_pow_mem)
                      [`N `H2])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj `y "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj
                       (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                       "."
                       `mem_of_pow_mem)
                      [`M `H3])]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                     ","
                     (Tactic.rwRule [] `eq1)]
                    "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `mul_mem_right
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `mul_mem_right
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app
                        `sum_mem
                        [(Term.hole "_")
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`i `hi]
                           []
                           "=>"
                           (Term.app
                            `mul_mem_left
                            [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
                  []
                  (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                   "generalize_proofs"
                   [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.proj
                    (Term.app `Classical.choose_spec [`h₂])
                    "."
                    (fieldIdx "1")))])])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.tacticExt1___
           "ext1"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.constructor "constructor")
           "<;>"
           (Tactic.intro "intro" [`hy]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.anonymousCtor "⟨" [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")] "⟩"))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Set.mem_preimage)
               ","
               (Tactic.rwRule [] `opens.mem_coe)
               ","
               (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
             [])
            []
            (Tactic.intro "intro" [`a_mem_y])
            []
            (Tactic.apply "apply" `hy)
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `to_fun)
               ","
               (Tactic.rwRule [] `mem_carrier_iff)
               ","
               (Tactic.rwRule [] `HomogeneousLocalization.val_mk')
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)]
              "]")
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `b_mem2)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                    [])]
                  "⟩")])
               [])])
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
                (Term.show
                 "show"
                 («term_=_»
                  (Term.typeAscription
                   "("
                   (Term.app
                    `mk
                    [`a
                     (Term.anonymousCtor
                      "⟨"
                      [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")]
                      "⟩")])
                   ":"
                   [(Term.app `away [`f])]
                   ")")
                  "="
                  («term_*_»
                   (Term.app
                    `mk
                    [(num "1")
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_^_» `f "^" `k)
                       ","
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
                      "⟩")])
                   "*"
                   (Term.app `mk [`a (num "1")])))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `mk_mul)
                        ","
                        (Tactic.rwRule [] `one_mul)
                        ","
                        (Tactic.rwRule [] `mul_one)]
                       "]")
                      [])
                     []
                     (Tactic.congr "congr" [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]")
                      [])])))))]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `Ideal.mul_mem_left
              [(Term.hole "_")
               (Term.hole "_")
               (Term.app
                `Ideal.subset_span
                [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.change
             "change"
             («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
             [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `hy)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Set.mem_preimage)
               ","
               (Tactic.rwRule [] `to_fun)
               ","
               (Tactic.rwRule [] `opens.mem_coe)
               ","
               (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
              "]")
             [])
            []
            (Tactic.intro "intro" [`rid])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             []
             []
             [(Tactic.location "at" (Tactic.locationHyp [`rid] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Algebra.smul_def)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Tactic.change
             "change"
             («term_=_»
              («term_*_»
               (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
               "*"
               (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
              "="
              (Term.app
               `mk
               [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
                 ", "
                 (Term.hole "_"))
                (Term.hole "_")]))
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mk_mul)
               ","
               (Tactic.rwRule [] `one_mul)
               ","
               (Tactic.rwRule [] `mk_eq_mk')
               ","
               (Tactic.rwRule [] `IsLocalization.eq)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `eq1)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
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
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `M)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                              [])]
                            "⟩")])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                 "."
                 `mem_or_mem)
                [(Term.show
                  "show"
                  («term_∈_»
                   («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
                   "∈"
                   (Term.hole "_"))
                  (Term.fromTerm "from" (Term.hole "_")))]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `H1)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `H3)])
                   [])
                  ")")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                 "."
                 `mem_or_mem)
                [`H1]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `H1)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `H2)])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `hy2 [`H1]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app
                (Term.proj `y "." (fieldIdx "2"))
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_of_pow_mem)
                  [`N `H2])]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app
                (Term.proj `y "." (fieldIdx "2"))
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
                   "."
                   `mem_of_pow_mem)
                  [`M `H3])]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
                 ","
                 (Tactic.rwRule [] `eq1)]
                "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                `mul_mem_right
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.app
                  `mul_mem_right
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app
                    `sum_mem
                    [(Term.hole "_")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`i `hi]
                       []
                       "=>"
                       (Term.app
                        `mul_mem_left
                        [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
              []
              (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
               "generalize_proofs"
               [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
               [])
              []
              (Tactic.exact
               "exact"
               (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.change
         "change"
         («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
         [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hy)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Set.mem_preimage)
           ","
           (Tactic.rwRule [] `to_fun)
           ","
           (Tactic.rwRule [] `opens.mem_coe)
           ","
           (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
          "]")
         [])
        []
        (Tactic.intro "intro" [`rid])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`rid] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Algebra.smul_def)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
        []
        (Tactic.change
         "change"
         («term_=_»
          («term_*_»
           (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
           "*"
           (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
          "="
          (Term.app
           `mk
           [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
             ", "
             (Term.hole "_"))
            (Term.hole "_")]))
         [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mk_mul)
           ","
           (Tactic.rwRule [] `one_mul)
           ","
           (Tactic.rwRule [] `mk_eq_mk')
           ","
           (Tactic.rwRule [] `IsLocalization.eq)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `eq1)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
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
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `M)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
            [(Term.show
              "show"
              («term_∈_»
               («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
               "∈"
               (Term.hole "_"))
              (Term.fromTerm "from" (Term.hole "_")))]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.one `H1) "|" (Std.Tactic.RCases.rcasesPat.one `H3)])
               [])
              ")")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
            [`H1]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.one `H1) "|" (Std.Tactic.RCases.rcasesPat.one `H2)])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `hy2 [`H1]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.app
            (Term.proj `y "." (fieldIdx "2"))
            [(Term.app
              (Term.proj
               (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
               "."
               `mem_of_pow_mem)
              [`N `H2])]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.app
            (Term.proj `y "." (fieldIdx "2"))
            [(Term.app
              (Term.proj
               (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
               "."
               `mem_of_pow_mem)
              [`M `H3])]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
             ","
             (Tactic.rwRule [] `eq1)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `mul_mem_right
            [(Term.hole "_")
             (Term.hole "_")
             (Term.app
              `mul_mem_right
              [(Term.hole "_")
               (Term.hole "_")
               (Term.app
                `sum_mem
                [(Term.hole "_")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `hi]
                   []
                   "=>"
                   (Term.app
                    `mul_mem_left
                    [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
          []
          (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
           "generalize_proofs"
           [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
           ","
           (Tactic.rwRule [] `eq1)]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `mul_mem_right
            [(Term.hole "_")
             (Term.hole "_")
             (Term.app
              `sum_mem
              [(Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
        []
        (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
         "generalize_proofs"
         [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Classical.choose_spec [`h₂]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Classical.choose_spec [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Classical.choose_spec [`h₂])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
       "generalize_proofs"
       [(Lean.binderIdent `h₁) (Lean.binderIdent `h₂)]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `mul_mem_right
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app
          `mul_mem_right
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `sum_mem
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [`i `hi]
               []
               "=>"
               (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `mul_mem_right
         [(Term.hole "_")
          (Term.hole "_")
          (Term.app
           `sum_mem
           [(Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [`i `hi]
              []
              "=>"
              (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_mem_right
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `sum_mem
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `hi]
            []
            "=>"
            (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sum_mem
       [(Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `hi]
          []
          "=>"
          (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `hi]
        []
        "=>"
        (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `mul_mem_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sum_mem
      [(Term.hole "_")
       (Term.fun
        "fun"
        (Term.basicFun
         [`i `hi]
         []
         "=>"
         (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_mem_right
      [(Term.hole "_")
       (Term.hole "_")
       (Term.paren
        "("
        (Term.app
         `sum_mem
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `hi]
            []
            "=>"
            (Term.app `mul_mem_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
        ")")])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem_right
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
        [(Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)]))
         ","
         (Tactic.rwRule [] `eq1)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(Term.hole "_") («term_^_» `f "^" `N)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `N) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
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
          (Term.proj `y "." (fieldIdx "2"))
          [(Term.app
            (Term.proj
             (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
             "."
             `mem_of_pow_mem)
            [`M `H3])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `y "." (fieldIdx "2"))
        [(Term.app
          (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
          [`M `H3])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `y "." (fieldIdx "2"))
       [(Term.app
         (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`M `H3])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
       [`M `H3])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H3
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
      [`M `H3])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
          (Term.proj `y "." (fieldIdx "2"))
          [(Term.app
            (Term.proj
             (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
             "."
             `mem_of_pow_mem)
            [`N `H2])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `y "." (fieldIdx "2"))
        [(Term.app
          (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
          [`N `H2])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `y "." (fieldIdx "2"))
       [(Term.app
         (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
         [`N `H2])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
       [`N `H2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_of_pow_mem)
      [`N `H2])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `hy2 [`H1]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hy2 [`H1]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hy2 [`H1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hy2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
          [`H1]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `H1) "|" (Std.Tactic.RCases.rcasesPat.one `H2)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
       [`H1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
          [(Term.show
            "show"
            («term_∈_»
             («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
             "∈"
             (Term.hole "_"))
            (Term.fromTerm "from" (Term.hole "_")))]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `H1) "|" (Std.Tactic.RCases.rcasesPat.one `H3)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
       [(Term.show
         "show"
         («term_∈_»
          («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
          "∈"
          (Term.hole "_"))
         (Term.fromTerm "from" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∈_»
        («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
        "∈"
        (Term.hole "_"))
       (Term.fromTerm "from" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_»
       («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
       "∈"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `M)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `a "*" («term_^_» `f "^" `N))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      («term_∈_»
       («term_*_» («term_*_» `a "*" («term_^_» `f "^" `N)) "*" («term_^_» `f "^" `M))
       "∈"
       (Term.hole "_"))
      (Term.fromTerm "from" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime) "." `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
       ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Submonoid.coe_one) "," (Tactic.rwRule [] `mul_one)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submonoid.coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `eq1)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `M)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mk_mul)
         ","
         (Tactic.rwRule [] `one_mul)
         ","
         (Tactic.rwRule [] `mk_eq_mk')
         ","
         (Tactic.rwRule [] `IsLocalization.eq)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsLocalization.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_eq_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_*_»
         (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
         "*"
         (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
        "="
        (Term.app
         `mk
         [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
           ", "
           (Term.hole "_"))
          (Term.hole "_")]))
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
        "*"
        (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
       "="
       (Term.app
        `mk
        [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
          ", "
          (Term.hole "_"))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk
       [(BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
         ", "
         (Term.hole "_"))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
       ", "
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent (Term.hole "_")) []))
      ", "
      (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
       "*"
       (Term.app `mk [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [(Term.hole "_") (Term.hole "_")])
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
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Localization.mk [(«term_^_» `f "^" `N) (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `f "^" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `N) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Algebra.smul_def)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `acd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq1)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_carrier.clear_denominator [`𝒜 (Term.hole "_") `rid])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rid
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_carrier.clear_denominator
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`rid] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`rid])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Set.mem_preimage)
         ","
         (Tactic.rwRule [] `to_fun)
         ","
         (Tactic.rwRule [] `opens.mem_coe)
         ","
         (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PrimeSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.mem_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hy1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_coe_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `hy)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
       [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (Term.proj `y "." (fieldIdx "1")) "∈" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.anonymousCtor "⟨" [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")] "⟩"))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Set.mem_preimage)
           ","
           (Tactic.rwRule [] `opens.mem_coe)
           ","
           (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
         [])
        []
        (Tactic.intro "intro" [`a_mem_y])
        []
        (Tactic.apply "apply" `hy)
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `to_fun)
           ","
           (Tactic.rwRule [] `mem_carrier_iff)
           ","
           (Tactic.rwRule [] `HomogeneousLocalization.val_mk')
           ","
           (Tactic.rwRule [] `Subtype.coe_mk)]
          "]")
         [])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `b_mem2)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                [])]
              "⟩")])
           [])])
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
            (Term.show
             "show"
             («term_=_»
              (Term.typeAscription
               "("
               (Term.app
                `mk
                [`a
                 (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
               ":"
               [(Term.app `away [`f])]
               ")")
              "="
              («term_*_»
               (Term.app
                `mk
                [(num "1")
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_^_» `f "^" `k)
                   ","
                   (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
                  "⟩")])
               "*"
               (Term.app `mk [`a (num "1")])))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mk_mul)
                    ","
                    (Tactic.rwRule [] `one_mul)
                    ","
                    (Tactic.rwRule [] `mul_one)]
                   "]")
                  [])
                 []
                 (Tactic.congr "congr" [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]")
                  [])])))))]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Ideal.mul_mem_left
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app
            `Ideal.subset_span
            [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Ideal.mul_mem_left
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app
          `Ideal.subset_span
          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mul_mem_left
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app
         `Ideal.subset_span
         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.subset_span
       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem_y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.subset_span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Ideal.subset_span
      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `a_mem_y "," `rfl] "⟩")])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_left
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
          (Term.show
           "show"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app
              `mk
              [`a (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
             ":"
             [(Term.app `away [`f])]
             ")")
            "="
            («term_*_»
             (Term.app
              `mk
              [(num "1")
               (Term.anonymousCtor
                "⟨"
                [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
                "⟩")])
             "*"
             (Term.app `mk [`a (num "1")])))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `mk_mul)
                  ","
                  (Tactic.rwRule [] `one_mul)
                  ","
                  (Tactic.rwRule [] `mul_one)]
                 "]")
                [])
               []
               (Tactic.congr "congr" [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]") [])])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app
          `mk
          [`a (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
         ":"
         [(Term.app `away [`f])]
         ")")
        "="
        («term_*_»
         (Term.app
          `mk
          [(num "1")
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
            "⟩")])
         "*"
         (Term.app `mk [`a (num "1")])))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mk_mul)
              ","
              (Tactic.rwRule [] `one_mul)
              ","
              (Tactic.rwRule [] `mul_one)]
             "]")
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]") [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mk_mul) "," (Tactic.rwRule [] `one_mul) "," (Tactic.rwRule [] `mul_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app
         `mk
         [`a (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
        ":"
        [(Term.app `away [`f])]
        ")")
       "="
       («term_*_»
        (Term.app
         `mk
         [(num "1")
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
           "⟩")])
        "*"
        (Term.app `mk [`a (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app
        `mk
        [(num "1")
         (Term.anonymousCtor
          "⟨"
          [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
          "⟩")])
       "*"
       (Term.app `mk [`a (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [`a (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `mk
       [(num "1")
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» `f "^" `k) "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
       "⟩")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `mk
        [`a (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
       ":"
       [(Term.app `away [`f])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk
       [`a (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `b_mem2)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b_mem2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `to_fun)
         ","
         (Tactic.rwRule [] `mem_carrier_iff)
         ","
         (Tactic.rwRule [] `HomogeneousLocalization.val_mk')
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HomogeneousLocalization.val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_carrier_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `hy)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a_mem_y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem_y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_coe_basic_open)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_coe_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Set.mem_preimage)
         ","
         (Tactic.rwRule [] `opens.mem_coe)
         ","
         (Tactic.rwRule [] `PrimeSpectrum.mem_basic_open)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PrimeSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.mem_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor "⟨" [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `y "." (fieldIdx "2")) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`hy]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`hy])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.«term_⁻¹'_»
        (Term.app `toFun [`𝒜 `f])
        " ⁻¹' "
        (Term.typeAscription
         "("
         (Term.app
          (Term.explicit "@" `PrimeSpectrum.basicOpen)
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
           (Term.hole "_")
           (Term.app
            `Quotient.mk'
            [(Term.anonymousCtor
              "⟨"
              [`k
               ","
               (Term.anonymousCtor "⟨" [`a "," `a_mem] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`b "," `b_mem1] "⟩")
               ","
               `b_mem2]
              "⟩")])])
         ":"
         [(Term.app
           `Set
           [(Term.app `PrimeSpectrum [(Term.app `HomogeneousLocalization.Away [`𝒜 `f])])])]
         ")"))
       "="
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
        "|"
        («term_∈_»
         (Term.proj `x "." (fieldIdx "1"))
         "∈"
         (Order.Basic.«term_⊓_»
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
          " ⊓ "
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
       "|"
       («term_∈_»
        (Term.proj `x "." (fieldIdx "1"))
        "∈"
        (Order.Basic.«term_⊓_»
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
         " ⊓ "
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.proj `x "." (fieldIdx "1"))
       "∈"
       (Order.Basic.«term_⊓_»
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
        " ⊓ "
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_»
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
       " ⊓ "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.637'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  preimage_eq
  ( a b : A ) ( k : ℕ ) ( a_mem : a ∈ 𝒜 k ) ( b_mem1 : b ∈ 𝒜 k ) ( b_mem2 : b ∈ Submonoid.powers f )
    :
      toFun 𝒜 f
          ⁻¹'
          (
            @ PrimeSpectrum.basicOpen
              A⁰_ f _ Quotient.mk' ⟨ k , ⟨ a , a_mem ⟩ , ⟨ b , b_mem1 ⟩ , b_mem2 ⟩
            :
            Set PrimeSpectrum HomogeneousLocalization.Away 𝒜 f
            )
        =
        { x | x . 1 ∈ pbo f ⊓ pbo a }
  :=
    by
      classical
        ext1 y
          constructor <;> intro hy
          ·
            refine' ⟨ y . 2 , _ ⟩
              rw [ Set.mem_preimage , opens.mem_coe , PrimeSpectrum.mem_basic_open ] at hy
              rw [ ProjectiveSpectrum.mem_coe_basic_open ]
              intro a_mem_y
              apply hy
              rw [ to_fun , mem_carrier_iff , HomogeneousLocalization.val_mk' , Subtype.coe_mk ]
              dsimp
              rcases b_mem2 with ⟨ k , hk ⟩
              simp
                only
                [
                  show
                    ( mk a ⟨ b , ⟨ k , hk ⟩ ⟩ : away f ) = mk 1 ⟨ f ^ k , ⟨ _ , rfl ⟩ ⟩ * mk a 1
                    by rw [ mk_mul , one_mul , mul_one ] congr rw [ hk ]
                  ]
              exact Ideal.mul_mem_left _ _ Ideal.subset_span ⟨ _ , a_mem_y , rfl ⟩
          ·
            change y . 1 ∈ _ at hy
              rcases hy with ⟨ hy1 , hy2 ⟩
              rw [ ProjectiveSpectrum.mem_coe_basic_open ] at hy1 hy2
              rw [ Set.mem_preimage , to_fun , opens.mem_coe , PrimeSpectrum.mem_basic_open ]
              intro rid
              dsimp at rid
              rcases mem_carrier.clear_denominator 𝒜 _ rid with ⟨ c , N , acd , eq1 ⟩
              rw [ Algebra.smul_def ] at eq1
              change Localization.mk f ^ N 1 * mk _ _ = mk ∑ _ , _ _ at eq1
              rw [ mk_mul , one_mul , mk_eq_mk' , IsLocalization.eq ] at eq1
              rcases eq1 with ⟨ ⟨ _ , ⟨ M , rfl ⟩ ⟩ , eq1 ⟩
              rw [ Submonoid.coe_one , mul_one ] at eq1
              simp only [ Subtype.coe_mk ] at eq1
              rcases y . 1 . IsPrime . mem_or_mem show a * f ^ N * f ^ M ∈ _ from _ with ( H1 | H3 )
              rcases y . 1 . IsPrime . mem_or_mem H1 with ( H1 | H2 )
              · exact hy2 H1
              · exact y . 2 y . 1 . IsPrime . mem_of_pow_mem N H2
              · exact y . 2 y . 1 . IsPrime . mem_of_pow_mem M H3
              ·
                rw [ mul_comm _ f ^ N , eq1 ]
                  refine'
                    mul_mem_right _ _ mul_mem_right _ _ sum_mem _ fun i hi => mul_mem_left _ _ _
                  generalize_proofs h₁ h₂
                  exact Classical.choose_spec h₂ . 1
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.preimage_eq AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_eq

end ToSpec

section

variable {𝒜}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic\nopen set in `Spec A⁰_f`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toSpec [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`f] [":" `A] "}")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»
           "Proj.T| "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))
          " ⟶ "
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" (Term.app `ToSpec.toFun [`𝒜 `f]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `continuous_to_fun
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.apply
                "apply"
                (Term.app
                 `is_topological_basis.continuous
                 [`PrimeSpectrum.is_topological_basis_basic_opens]))
               []
               (Std.Tactic.rintro
                "rintro"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
                 (Std.Tactic.RCases.rintroPat.one
                  (Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `a)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `ha)])
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
                                [(Std.Tactic.RCases.rcasesPat.one `b)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `hb1)])
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
                                [(Std.Tactic.RCases.rcasesPat.one `k')])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `hb2)])
                               [])]
                             "⟩")])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩"))]
                [])
               ";"
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app
                    `to_Spec.preimage_eq
                    [`f `a `b `k `ha `hb1 (Term.anonymousCtor "⟨" [`k' "," `hb2] "⟩")]))]
                 "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 `is_open_induced_iff.mpr
                 [(Term.anonymousCtor
                   "⟨"
                   [(Order.Basic.«term_⊓_»
                     (Term.proj
                      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_
                       "pbo "
                       `f)
                      "."
                      (fieldIdx "1"))
                     " ⊓ "
                     (Term.proj
                      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_
                       "pbo "
                       `a)
                      "."
                      (fieldIdx "1")))
                    ","
                    (Term.app
                     `IsOpen.inter
                     [(Term.proj
                       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_
                        "pbo "
                        `f)
                       "."
                       (fieldIdx "2"))
                      (Term.proj
                       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_
                        "pbo "
                        `a)
                       "."
                       (fieldIdx "2"))])
                    ","
                    (Term.hole "_")]
                   "⟩")]))
               []
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `z))]
                [])
               ";"
               (Tactic.«tactic_<;>_»
                (Tactic.«tactic_<;>_»
                 (Tactic.constructor "constructor")
                 "<;>"
                 (Tactic.intro "intro" [`hz]))
                "<;>"
                (Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  []
                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Set.mem_preimage)] "]")]
                  [])))]))))))]
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
         [(Tactic.apply
           "apply"
           (Term.app
            `is_topological_basis.continuous
            [`PrimeSpectrum.is_topological_basis_basic_opens]))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb1)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k')])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb2)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          ";"
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `to_Spec.preimage_eq
               [`f `a `b `k `ha `hb1 (Term.anonymousCtor "⟨" [`k' "," `hb2] "⟩")]))]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `is_open_induced_iff.mpr
            [(Term.anonymousCtor
              "⟨"
              [(Order.Basic.«term_⊓_»
                (Term.proj
                 (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
                 "."
                 (fieldIdx "1"))
                " ⊓ "
                (Term.proj
                 (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
                 "."
                 (fieldIdx "1")))
               ","
               (Term.app
                `IsOpen.inter
                [(Term.proj
                  (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
                  "."
                  (fieldIdx "2"))
                 (Term.proj
                  (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
                  "."
                  (fieldIdx "2"))])
               ","
               (Term.hole "_")]
              "⟩")]))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `z))]
           [])
          ";"
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.constructor "constructor")
            "<;>"
            (Tactic.intro "intro" [`hz]))
           "<;>"
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Set.mem_preimage)] "]")]
             [])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`hz]))
       "<;>"
       (Std.Tactic.Simpa.simpa
        "simpa"
        []
        []
        (Std.Tactic.Simpa.simpaArgsRest
         []
         []
         []
         [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Set.mem_preimage)] "]")]
         [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Set.mem_preimage)] "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`hz]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`hz])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `z))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `is_open_induced_iff.mpr
        [(Term.anonymousCtor
          "⟨"
          [(Order.Basic.«term_⊓_»
            (Term.proj
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
             "."
             (fieldIdx "1"))
            " ⊓ "
            (Term.proj
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
             "."
             (fieldIdx "1")))
           ","
           (Term.app
            `IsOpen.inter
            [(Term.proj
              (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
              "."
              (fieldIdx "2"))
             (Term.proj
              (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
              "."
              (fieldIdx "2"))])
           ","
           (Term.hole "_")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_open_induced_iff.mpr
       [(Term.anonymousCtor
         "⟨"
         [(Order.Basic.«term_⊓_»
           (Term.proj
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
            "."
            (fieldIdx "1"))
           " ⊓ "
           (Term.proj
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
            "."
            (fieldIdx "1")))
          ","
          (Term.app
           `IsOpen.inter
           [(Term.proj
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
             "."
             (fieldIdx "2"))
            (Term.proj
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
             "."
             (fieldIdx "2"))])
          ","
          (Term.hole "_")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Order.Basic.«term_⊓_»
         (Term.proj
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
          "."
          (fieldIdx "1"))
         " ⊓ "
         (Term.proj
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
          "."
          (fieldIdx "1")))
        ","
        (Term.app
         `IsOpen.inter
         [(Term.proj
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
           "."
           (fieldIdx "2"))
          (Term.proj
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
           "."
           (fieldIdx "2"))])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsOpen.inter
       [(Term.proj
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)
         "."
         (fieldIdx "2"))
        (Term.proj
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
         "."
         (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.637'
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
    The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
    open set in `Spec A⁰_f`.
    -/
  def
    toSpec
    { f : A } : Proj.T| pbo f ⟶ Spec.T A⁰_ f
    where
      toFun := ToSpec.toFun 𝒜 f
        continuous_to_fun
          :=
          by
            apply is_topological_basis.continuous PrimeSpectrum.is_topological_basis_basic_opens
              rintro _ ⟨ ⟨ k , ⟨ a , ha ⟩ , ⟨ b , hb1 ⟩ , ⟨ k' , hb2 ⟩ ⟩ , rfl ⟩
              ;
              dsimp
              erw [ to_Spec.preimage_eq f a b k ha hb1 ⟨ k' , hb2 ⟩ ]
              refine'
                is_open_induced_iff.mpr
                  ⟨ pbo f . 1 ⊓ pbo a . 1 , IsOpen.inter pbo f . 2 pbo a . 2 , _ ⟩
              ext z
              ;
              constructor <;> intro hz <;> simpa [ Set.mem_preimage ]
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec

end

namespace FromSpec

open GradedAlgebra SetLike

open Finset hiding mk_zero

open _Root_.HomogeneousLocalization

variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def mem_tac : tactic Unit :=
  let b : tactic Unit := sorry
  b <|> sorry
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_tac algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_tac

include f_deg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending\n`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the\nelements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power\nof the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,\nlies in `q`.\n\nThe set `{a | aᵢᵐ/fⁱ ∈ q}`\n* is an ideal, as proved in `carrier.as_ideal`;\n* is homogeneous, as proved in `carrier.as_homogeneous_ideal`;\n* is prime, as proved in `carrier.as_ideal.prime`;\n* is relevant, as proved in `carrier.relevant`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `carrier [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`q]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `Set [`A]))])
      (Command.declValSimple
       ":="
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
        "|"
        (Term.forall
         "∀"
         [`i]
         []
         ","
         («term_∈_»
          (Term.typeAscription
           "("
           (Term.app
            `Quotient.mk'
            [(Term.anonymousCtor
              "⟨"
              [(«term_*_» `m "*" `i)
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                "⟩")
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_^_» `f "^" `i)
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                       [])
                      "<;>"
                      (Mathlib.RunCmd.runTac
                       "run_tac"
                       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                "⟩")
               ","
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
              "⟩")])
           ":"
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
           ")")
          "∈"
          (Term.proj `q "." (fieldIdx "1"))))
        "}")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
       "|"
       (Term.forall
        "∀"
        [`i]
        []
        ","
        («term_∈_»
         (Term.typeAscription
          "("
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» `f "^" `i)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
             "⟩")])
          ":"
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
          ")")
         "∈"
         (Term.proj `q "." (fieldIdx "1"))))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       []
       ","
       («term_∈_»
        (Term.typeAscription
         "("
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» `f "^" `i)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
            "⟩")])
         ":"
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
         ")")
        "∈"
        (Term.proj `q "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription
        "("
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» `f "^" `i)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
           "⟩")])
        ":"
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
        ")")
       "∈"
       (Term.proj `q "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `i)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
          "⟩")])
       ":"
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
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
    The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending
    `q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the
    elements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power
    of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,
    lies in `q`.
    
    The set `{a | aᵢᵐ/fⁱ ∈ q}`
    * is an ideal, as proved in `carrier.as_ideal`;
    * is homogeneous, as proved in `carrier.as_homogeneous_ideal`;
    * is prime, as proved in `carrier.as_ideal.prime`;
    * is relevant, as proved in `carrier.relevant`.
    -/
  def
    carrier
    ( q : Spec.T A⁰_ f ) : Set A
    :=
      {
        a
        |
        ∀
          i
          ,
          (
              Quotient.mk'
                ⟨
                  m * i
                    ,
                    ⟨ proj 𝒜 i a ^ m , by run_tac mem_tac ⟩
                    ,
                    ⟨ f ^ i , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                    ,
                    ⟨ _ , rfl ⟩
                  ⟩
              :
              A⁰_ f
              )
            ∈
            q . 1
        }
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_carrier_iff [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`q]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))]
         []
         ")")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))
         "↔"
         (Term.forall
          "∀"
          [`i]
          []
          ","
          («term_∈_»
           (Term.typeAscription
            "("
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(«term_*_» `m "*" `i)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.RunCmd.runTac
                       "run_tac"
                       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» `f "^" `i)
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                        [])
                       "<;>"
                       (Mathlib.RunCmd.runTac
                        "run_tac"
                        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
               "⟩")])
            ":"
            [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
            ")")
           "∈"
           (Term.proj `q "." (fieldIdx "1")))))))
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
       («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))
       "↔"
       (Term.forall
        "∀"
        [`i]
        []
        ","
        («term_∈_»
         (Term.typeAscription
          "("
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» `f "^" `i)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
             "⟩")])
          ":"
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
          ")")
         "∈"
         (Term.proj `q "." (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       []
       ","
       («term_∈_»
        (Term.typeAscription
         "("
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» `f "^" `i)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
            "⟩")])
         ":"
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
         ")")
        "∈"
        (Term.proj `q "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription
        "("
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» `f "^" `i)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
           "⟩")])
        ":"
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
        ")")
       "∈"
       (Term.proj `q "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `i)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]
          "⟩")])
       ":"
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_carrier_iff
  ( q : Spec.T A⁰_ f ) ( a : A )
    :
      a ∈ carrier f_deg q
        ↔
        ∀
          i
          ,
          (
              Quotient.mk'
                ⟨
                  m * i
                    ,
                    ⟨ proj 𝒜 i a ^ m , by run_tac mem_tac ⟩
                    ,
                    ⟨ f ^ i , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                    ,
                    ⟨ _ , rfl ⟩
                  ⟩
              :
              A⁰_ f
              )
            ∈
            q . 1
  := Iff.rfl
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_carrier_iff AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_carrier_iff' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`q]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))]
         []
         ")")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))
         "↔"
         (Term.forall
          "∀"
          [`i]
          []
          ","
          («term_∈_»
           (Term.typeAscription
            "("
            (Term.app
             `Localization.mk
             [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
               "⟩")])
            ":"
            [(Term.app `Localization.Away [`f])]
            ")")
           "∈"
           (Set.Data.Set.Image.term_''_
            (Term.app
             `algebraMap
             [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
            " '' "
            (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1"))))))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `mem_carrier_iff [`f_deg `q `a]) "." `trans)
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Tactic.constructor "constructor")
               "<;>"
               (Tactic.intro "intro" [`h `i]))
              "<;>"
              (Tactic.specialize "specialize" (Term.app `h [`i])))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `h)]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                       [])]
                     "⟩")])
                  [])])
               []
               (convert "convert" [] `h [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
                 "]")
                [])
               []
               (Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
                [])
               []
               (Tactic.tacticRfl "rfl")])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `mem_carrier_iff [`f_deg `q `a]) "." `trans)
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Tactic.constructor "constructor")
              "<;>"
              (Tactic.intro "intro" [`h `i]))
             "<;>"
             (Tactic.specialize "specialize" (Term.app `h [`i])))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `h)]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                      [])]
                    "⟩")])
                 [])])
              []
              (convert "convert" [] `h [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
                "]")
               [])
              []
              (Tactic.dsimp
               "dsimp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
               [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
               [])
              []
              (Tactic.tacticRfl "rfl")])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.constructor "constructor")
            "<;>"
            (Tactic.intro "intro" [`h `i]))
           "<;>"
           (Tactic.specialize "specialize" (Term.app `h [`i])))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]") [])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `h)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                    [])]
                  "⟩")])
               [])])
            []
            (convert "convert" [] `h [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
              "]")
             [])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `h)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                [])]
              "⟩")])
           [])])
        []
        (convert "convert" [] `h [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
          "]")
         [])
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `h [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]") [])
        []
        (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.constructor "constructor")
        "<;>"
        (Tactic.intro "intro" [`h `i]))
       "<;>"
       (Tactic.specialize "specialize" (Term.app `h [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.specialize "specialize" (Term.app `h [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`h `i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h `i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
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
          (Tactic.«tactic_<;>_»
           (Tactic.constructor "constructor")
           "<;>"
           (Tactic.intro "intro" [`h `i]))
          "<;>"
          (Tactic.specialize "specialize" (Term.app `h [`i])))
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]") [])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h "," `rfl] "⟩"))])
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_image)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `h)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                   [])]
                 "⟩")])
              [])])
           []
           (convert "convert" [] `h [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
             "]")
            [])
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)] "]")
            [])
           []
           (Tactic.tacticRfl "rfl")])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `mem_carrier_iff [`f_deg `q `a]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mem_carrier_iff [`f_deg `q `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_carrier_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mem_carrier_iff [`f_deg `q `a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))
       "↔"
       (Term.forall
        "∀"
        [`i]
        []
        ","
        («term_∈_»
         (Term.typeAscription
          "("
          (Term.app
           `Localization.mk
           [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
             "⟩")])
          ":"
          [(Term.app `Localization.Away [`f])]
          ")")
         "∈"
         (Set.Data.Set.Image.term_''_
          (Term.app
           `algebraMap
           [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
          " '' "
          (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       []
       ","
       («term_∈_»
        (Term.typeAscription
         "("
         (Term.app
          `Localization.mk
          [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
            "⟩")])
         ":"
         [(Term.app `Localization.Away [`f])]
         ")")
        "∈"
        (Set.Data.Set.Image.term_''_
         (Term.app
          `algebraMap
          [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
         " '' "
         (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription
        "("
        (Term.app
         `Localization.mk
         [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
           "⟩")])
        ":"
        [(Term.app `Localization.Away [`f])]
        ")")
       "∈"
       (Set.Data.Set.Image.term_''_
        (Term.app
         `algebraMap
         [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
        " '' "
        (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app
        `algebraMap
        [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
       " '' "
       (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `q "." (fieldIdx "1")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `algebraMap
       [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Localization.Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `HomogeneousLocalization.Away [`𝒜 `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HomogeneousLocalization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `HomogeneousLocalization.Away [`𝒜 `f])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `Localization.mk
        [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
         (Term.anonymousCtor
          "⟨"
          [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
          "⟩")])
       ":"
       [(Term.app `Localization.Away [`f])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Localization.mk
       [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» `f "^" `i) "," (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `f "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier [`f_deg `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
       "Spec.T "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termSpec.T_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2382'
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
  mem_carrier_iff'
  ( q : Spec.T A⁰_ f ) ( a : A )
    :
      a ∈ carrier f_deg q
        ↔
        ∀
          i
          ,
          ( Localization.mk proj 𝒜 i a ^ m ⟨ f ^ i , ⟨ i , rfl ⟩ ⟩ : Localization.Away f )
            ∈
            algebraMap HomogeneousLocalization.Away 𝒜 f Localization.Away f '' q . 1 . 1
  :=
    mem_carrier_iff f_deg q a . trans
      by
        constructor <;> intro h i <;> specialize h i
          · rw [ Set.mem_image ] refine' ⟨ _ , h , rfl ⟩
          ·
            rw [ Set.mem_image ] at h
              rcases h with ⟨ x , h , hx ⟩
              convert h
              rw [ ext_iff_val , val_mk' ]
              dsimp only [ Subtype.coe_mk ]
              rw [ ← hx ]
              rfl
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_carrier_iff' AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `carrier.add_mem [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`q]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))]
         []
         ")")
        (Term.implicitBinder "{" [`a `b] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":" («term_∈_» `a "∈" (Term.app `carrier [`f_deg `q]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hb]
         [":" («term_∈_» `b "∈" (Term.app `carrier [`f_deg `q]))]
         []
         ")")]
       (Term.typeSpec ":" («term_∈_» («term_+_» `a "+" `b) "∈" (Term.app `carrier [`f_deg `q]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.fun
             "fun"
             (Term.basicFun
              [`i]
              []
              "=>"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.proj `q "." (fieldIdx "2")) "." `mem_or_mem)
                 [(Term.hole "_")])
                "."
                `elim)
               [`id `id]))))
           []
           (Tactic.change
            "change"
            («term_∈_»
             (Term.typeAscription
              "("
              (Term.app
               `Quotient.mk'
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
                 "⟩")])
              ":"
              [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
              ")")
             "∈"
             (Term.proj `q "." (fieldIdx "1")))
            [])
           ";"
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
              ","
              (Tactic.rwRule [] `map_add)
              ","
              (Tactic.rwRule [] `add_pow)
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nsmul_eq_mul)]
             "]")
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `g
              []
              [(Term.typeSpec
                ":"
                (Term.arrow
                 (termℕ "ℕ")
                 "→"
                 (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»
                  "A⁰_ "
                  `f)))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`j]
                []
                "=>"
                (Algebra.Group.Defs.«term_•_»
                 (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
                 " • "
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h2)
                  ":"
                  («term_<_» («term_+_» `m "+" `m) "<" `j)
                  "then"
                  (num "0")
                  "else"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h1)
                   ":"
                   («term_≤_» `j "≤" `m)
                   "then"
                   («term_*_»
                    (Term.app
                     `Quotient.mk'
                     [(Term.anonymousCtor
                       "⟨"
                       [(«term_*_» `m "*" `i)
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(«term_*_»
                           («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                           "*"
                           («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
                          ","
                          (Term.hole "_")]
                         "⟩")
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(Term.hole "_")
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                                [])
                               "<;>"
                               (Mathlib.RunCmd.runTac
                                "run_tac"
                                (Term.doSeqIndent
                                 [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                       "⟩")])
                    "*"
                    (Term.app
                     `Quotient.mk'
                     [(Term.anonymousCtor
                       "⟨"
                       [(«term_*_» `m "*" `i)
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(Term.hole "_")
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                                [])
                               "<;>"
                               (Mathlib.RunCmd.runTac
                                "run_tac"
                                (Term.doSeqIndent
                                 [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                       "⟩")]))
                   "else"
                   («term_*_»
                    (Term.app
                     `Quotient.mk'
                     [(Term.anonymousCtor
                       "⟨"
                       [(«term_*_» `m "*" `i)
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(Term.hole "_")
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                                [])
                               "<;>"
                               (Mathlib.RunCmd.runTac
                                "run_tac"
                                (Term.doSeqIndent
                                 [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                       "⟩")])
                    "*"
                    (Term.app
                     `Quotient.mk'
                     [(Term.anonymousCtor
                       "⟨"
                       [(«term_*_» `m "*" `i)
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(«term_*_»
                           («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                           "*"
                           («term_^_»
                            (Term.app `proj [`𝒜 `i `b])
                            "^"
                            («term_-_» («term_+_» `m "+" `m) "-" `j)))
                          ","
                          (Term.hole "_")]
                         "⟩")
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(Term.hole "_")
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                                [])
                               "<;>"
                               (Mathlib.RunCmd.runTac
                                "run_tac"
                                (Term.doSeqIndent
                                 [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                         "⟩")
                        ","
                        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                       "⟩")]))))))))))
           []
           (Tactic.rotateLeft "rotate_left" [])
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
                 (Term.typeAscription
                  "("
                  (Term.hole "_")
                  ":"
                  [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
                  ")"))]
               "]")
              [])
             []
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)
                ","
                (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h1]))]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])
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
                 (Term.typeAscription
                  "("
                  (Term.hole "_")
                  ":"
                  [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
                  ")"))]
               "]")
              [])
             []
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)]
               "]")
              [])
             []
             (Tactic.congr "congr" [])
             []
             (Mathlib.Tactic.Zify.zify
              "zify"
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] (Term.app `le_of_not_lt [`h2]))
                 ","
                 (Tactic.simpLemma [] [] (Term.app `le_of_not_le [`h1]))]
                "]")]
              [])
             []
             (Tactic.abel "abel" [] [])])
           []
           (convertTo
            "convert_to"
            («term_∈_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              " in "
              (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
              ", "
              (Term.app `g [`i]))
             "∈"
             (Term.proj `q "." (fieldIdx "1")))
            [])
           ";"
           (Mathlib.Tactic.tacticSwap "swap")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`j `hj]
                  []
                  "=>"
                  (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))]))
             []
             (Mathlib.Tactic.splitIfs "split_ifs" [] [])
             []
             (Std.Tactic.exacts
              "exacts"
              "["
              [(Term.proj (Term.proj `q "." (fieldIdx "1")) "." `zero_mem)
               ","
               (Term.app
                (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
                [(Term.hole "_") (Term.app `hb [`i])])
               ","
               (Term.app
                (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
                [(Term.hole "_") (Term.app `ha [`i])])]
              "]")])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.hole "_")
             "="
             (Term.app
              (Term.app
               `algebraMap
               [(Term.app `HomogeneousLocalization.Away [`𝒜 `f])
                (Term.app `Localization.Away [`f])])
              [(Term.hole "_")]))
            [])
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
            [])
           ";"
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum) "," (Tactic.rwRule [] `mk_sum)] "]")
            [])
           []
           (Tactic.apply
            "apply"
            (Term.app
             `Finset.sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.hole "_")
             "="
             (Term.app `HomogeneousLocalization.val [(Term.hole "_")]))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.smul_val)] "]")
            [])
           []
           (Mathlib.Tactic.splitIfs
            "split_ifs"
            []
            ["with" [(Lean.binderIdent `h2) (Lean.binderIdent `h1)]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj])
                 "."
                 `not_le)
                [`h2])
               "."
               `elim))])
           []
           (Tactic.allGoals
            "all_goals"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `mul_val)
                  ","
                  (Tactic.simpLemma [] [] `zero_val)
                  ","
                  (Tactic.simpLemma [] [] `val_mk')
                  ","
                  (Tactic.simpLemma [] [] `Subtype.coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `mk_mul)
                  ","
                  (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mk)]
                 "]"]
                [])
               ";"
               (Tactic.congr "congr" [(num "2")])])))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mul_assoc)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
                ","
                (Tactic.rwRule [] (Term.app `add_comm [(«term_-_» `m "-" `j)]))
                ","
                (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h1]))]
               "]")
              [])])
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
                ","
                (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [(Term.app `le_of_not_le [`h1])]))]
               "]")
              [])])
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])])))
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
           (Term.fun
            "fun"
            (Term.basicFun
             [`i]
             []
             "=>"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.proj `q "." (fieldIdx "2")) "." `mem_or_mem)
                [(Term.hole "_")])
               "."
               `elim)
              [`id `id]))))
          []
          (Tactic.change
           "change"
           («term_∈_»
            (Term.typeAscription
             "("
             (Term.app
              `Quotient.mk'
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
                "⟩")])
             ":"
             [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
             ")")
            "∈"
            (Term.proj `q "." (fieldIdx "1")))
           [])
          ";"
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
             ","
             (Tactic.rwRule [] `map_add)
             ","
             (Tactic.rwRule [] `add_pow)
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nsmul_eq_mul)]
            "]")
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `g
             []
             [(Term.typeSpec
               ":"
               (Term.arrow
                (termℕ "ℕ")
                "→"
                (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»
                 "A⁰_ "
                 `f)))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`j]
               []
               "=>"
               (Algebra.Group.Defs.«term_•_»
                (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
                " • "
                (termDepIfThenElse
                 "if"
                 (Lean.binderIdent `h2)
                 ":"
                 («term_<_» («term_+_» `m "+" `m) "<" `j)
                 "then"
                 (num "0")
                 "else"
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h1)
                  ":"
                  («term_≤_» `j "≤" `m)
                  "then"
                  («term_*_»
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(«term_*_» `m "*" `i)
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_*_»
                          («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                          "*"
                          («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
                         ","
                         (Term.hole "_")]
                        "⟩")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.hole "_")
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                               [])
                              "<;>"
                              (Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent
                                [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                      "⟩")])
                   "*"
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(«term_*_» `m "*" `i)
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Mathlib.RunCmd.runTac
                              "run_tac"
                              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.hole "_")
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                               [])
                              "<;>"
                              (Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent
                                [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                      "⟩")]))
                  "else"
                  («term_*_»
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(«term_*_» `m "*" `i)
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Mathlib.RunCmd.runTac
                              "run_tac"
                              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.hole "_")
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                               [])
                              "<;>"
                              (Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent
                                [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                      "⟩")])
                   "*"
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(«term_*_» `m "*" `i)
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_*_»
                          («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                          "*"
                          («term_^_»
                           (Term.app `proj [`𝒜 `i `b])
                           "^"
                           («term_-_» («term_+_» `m "+" `m) "-" `j)))
                         ","
                         (Term.hole "_")]
                        "⟩")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.hole "_")
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                               [])
                              "<;>"
                              (Mathlib.RunCmd.runTac
                               "run_tac"
                               (Term.doSeqIndent
                                [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                      "⟩")]))))))))))
          []
          (Tactic.rotateLeft "rotate_left" [])
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
                (Term.typeAscription
                 "("
                 (Term.hole "_")
                 ":"
                 [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
                 ")"))]
              "]")
             [])
            []
            (Mathlib.RunCmd.runTac
             "run_tac"
             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)
               ","
               (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h1]))]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])
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
                (Term.typeAscription
                 "("
                 (Term.hole "_")
                 ":"
                 [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
                 ")"))]
              "]")
             [])
            []
            (Mathlib.RunCmd.runTac
             "run_tac"
             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)]
              "]")
             [])
            []
            (Tactic.congr "congr" [])
            []
            (Mathlib.Tactic.Zify.zify
             "zify"
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] (Term.app `le_of_not_lt [`h2]))
                ","
                (Tactic.simpLemma [] [] (Term.app `le_of_not_le [`h1]))]
               "]")]
             [])
            []
            (Tactic.abel "abel" [] [])])
          []
          (convertTo
           "convert_to"
           («term_∈_»
            (BigOperators.Algebra.BigOperators.Basic.finset.sum
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             " in "
             (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
             ", "
             (Term.app `g [`i]))
            "∈"
            (Term.proj `q "." (fieldIdx "1")))
           [])
          ";"
          (Mathlib.Tactic.tacticSwap "swap")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`j `hj]
                 []
                 "=>"
                 (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))]))
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            (Std.Tactic.exacts
             "exacts"
             "["
             [(Term.proj (Term.proj `q "." (fieldIdx "1")) "." `zero_mem)
              ","
              (Term.app
               (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
               [(Term.hole "_") (Term.app `hb [`i])])
              ","
              (Term.app
               (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
               [(Term.hole "_") (Term.app `ha [`i])])]
             "]")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.hole "_")
            "="
            (Term.app
             (Term.app
              `algebraMap
              [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
             [(Term.hole "_")]))
           [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
           [])
          ";"
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum) "," (Tactic.rwRule [] `mk_sum)] "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `Finset.sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.change
           "change"
           («term_=_» (Term.hole "_") "=" (Term.app `HomogeneousLocalization.val [(Term.hole "_")]))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.smul_val)] "]")
           [])
          []
          (Mathlib.Tactic.splitIfs
           "split_ifs"
           []
           ["with" [(Lean.binderIdent `h2) (Lean.binderIdent `h1)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               (Term.proj
                (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj])
                "."
                `not_le)
               [`h2])
              "."
              `elim))])
          []
          (Tactic.allGoals
           "all_goals"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `mul_val)
                 ","
                 (Tactic.simpLemma [] [] `zero_val)
                 ","
                 (Tactic.simpLemma [] [] `val_mk')
                 ","
                 (Tactic.simpLemma [] [] `Subtype.coe_mk)
                 ","
                 (Tactic.simpLemma [] [] `mk_mul)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mk)]
                "]"]
               [])
              ";"
              (Tactic.congr "congr" [(num "2")])])))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
               ","
               (Tactic.rwRule [] (Term.app `add_comm [(«term_-_» `m "-" `j)]))
               ","
               (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h1]))]
              "]")
             [])])
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
               ","
               (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [(Term.app `le_of_not_le [`h1])]))]
              "]")
             [])])
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
           ","
           (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [(Term.app `le_of_not_le [`h1])]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [(Term.app `le_of_not_le [`h1])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_of_le [(Term.app `le_of_not_le [`h1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_not_le [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_not_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_not_le [`h1]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          [(Tactic.rwRule [] `mul_assoc)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
           ","
           (Tactic.rwRule [] (Term.app `add_comm [(«term_-_» `m "-" `j)]))
           ","
           (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h1]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
         ","
         (Tactic.rwRule [] (Term.app `add_comm [(«term_-_» `m "-" `j)]))
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h1]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_assoc [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_comm [(«term_-_» `m "-" `j)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `m "-" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `m "-" `j) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `mul_val)
             ","
             (Tactic.simpLemma [] [] `zero_val)
             ","
             (Tactic.simpLemma [] [] `val_mk')
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_mk)
             ","
             (Tactic.simpLemma [] [] `mk_mul)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mk)]
            "]"]
           [])
          ";"
          (Tactic.congr "congr" [(num "2")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "2")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mul_val)
         ","
         (Tactic.simpLemma [] [] `zero_val)
         ","
         (Tactic.simpLemma [] [] `val_mk')
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `mk_mul)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_mul
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
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_val
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
           (Term.proj (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) "." `not_le)
           [`h2])
          "."
          `elim))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         (Term.proj (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) "." `not_le)
         [`h2])
        "."
        `elim))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) "." `not_le)
        [`h2])
       "."
       `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) "." `not_le)
       [`h2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) "." `not_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Finset.mem_range "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Finset.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "1")) [`hj]) ")")
       "."
       `not_le)
      [`h2])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs
       "split_ifs"
       []
       ["with" [(Lean.binderIdent `h2) (Lean.binderIdent `h1)]])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `HomogeneousLocalization.smul_val)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HomogeneousLocalization.smul_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_» (Term.hole "_") "=" (Term.app `HomogeneousLocalization.val [(Term.hole "_")]))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `HomogeneousLocalization.val [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HomogeneousLocalization.val [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HomogeneousLocalization.val
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `Finset.sum_congr
        [`rfl (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.sum_congr
       [`rfl (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.sum_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum) "," (Tactic.rwRule [] `mk_sum)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.hole "_")
        "="
        (Term.app
         (Term.app
          `algebraMap
          [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
         [(Term.hole "_")]))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Term.app
        (Term.app
         `algebraMap
         [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        `algebraMap
        [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `algebraMap
       [(Term.app `HomogeneousLocalization.Away [`𝒜 `f]) (Term.app `Localization.Away [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.Away [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Localization.Away [`f]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `HomogeneousLocalization.Away [`𝒜 `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HomogeneousLocalization.Away
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `HomogeneousLocalization.Away [`𝒜 `f])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `algebraMap
      [(Term.paren "(" (Term.app `HomogeneousLocalization.Away [`𝒜 `f]) ")")
       (Term.paren "(" (Term.app `Localization.Away [`f]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val) "," (Tactic.rwRule [] `val_mk')] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`j `hj]
             []
             "=>"
             (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))]))
        []
        (Mathlib.Tactic.splitIfs "split_ifs" [] [])
        []
        (Std.Tactic.exacts
         "exacts"
         "["
         [(Term.proj (Term.proj `q "." (fieldIdx "1")) "." `zero_mem)
          ","
          (Term.app
           (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
           [(Term.hole "_") (Term.app `hb [`i])])
          ","
          (Term.app
           (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
           [(Term.hole "_") (Term.app `ha [`i])])]
         "]")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts
       "exacts"
       "["
       [(Term.proj (Term.proj `q "." (fieldIdx "1")) "." `zero_mem)
        ","
        (Term.app
         (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
         [(Term.hole "_") (Term.app `hb [`i])])
        ","
        (Term.app
         (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
         [(Term.hole "_") (Term.app `ha [`i])])]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
       [(Term.hole "_") (Term.app `ha [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ha [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
       [(Term.hole "_") (Term.app `hb [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hb [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hb [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `mul_mem_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `zero_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`j `hj]
           []
           "=>"
           (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
       [(Term.fun
         "fun"
         (Term.basicFun [`j `hj] [] "=>" (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`j `hj] [] "=>" (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nsmul_mem [(Term.hole "_") (Term.hole "_")])
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
      `nsmul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `q "." (fieldIdx "1")) "." `sum_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSwap "swap")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convertTo
       "convert_to"
       («term_∈_»
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
         ", "
         (Term.app `g [`i]))
        "∈"
        (Term.proj `q "." (fieldIdx "1")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
        ", "
        (Term.app `g [`i]))
       "∈"
       (Term.proj `q "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
       ", "
       (Term.app `g [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(«term_+_» («term_+_» `m "+" `m) "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_+_» `m "+" `m) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `m "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_+_» `m "+" `m) "+" (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum
      "∑"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
      " in "
      (Term.app `range [(Term.paren "(" («term_+_» («term_+_» `m "+" `m) "+" (num "1")) ")")])
      ", "
      (Term.app `g [`i]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.typeAscription
             "("
             (Term.hole "_")
             ":"
             [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
             ")"))]
          "]")
         [])
        []
        (Mathlib.RunCmd.runTac
         "run_tac"
         (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)] "]")
         [])
        []
        (Tactic.congr "congr" [])
        []
        (Mathlib.Tactic.Zify.zify
         "zify"
         [(Tactic.simpArgs
           "["
           [(Tactic.simpLemma [] [] (Term.app `le_of_not_lt [`h2]))
            ","
            (Tactic.simpLemma [] [] (Term.app `le_of_not_le [`h1]))]
           "]")]
         [])
        []
        (Tactic.abel "abel" [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Zify.zify
       "zify"
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] (Term.app `le_of_not_lt [`h2]))
          ","
          (Tactic.simpLemma [] [] (Term.app `le_of_not_le [`h1]))]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_not_le [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_not_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_not_lt [`h2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.typeAscription
           "("
           (Term.hole "_")
           ":"
           [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
           ")"))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.hole "_")
       ":"
       [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          [(Tactic.rwRule
            []
            (Term.typeAscription
             "("
             (Term.hole "_")
             ":"
             [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
             ")"))]
          "]")
         [])
        []
        (Mathlib.RunCmd.runTac
         "run_tac"
         (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)
           ","
           (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h1]))]
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_smul)
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h1]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_of_le [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.typeAscription
           "("
           (Term.hole "_")
           ":"
           [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
           ")"))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.hole "_")
       ":"
       [(«term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_*_» `m "*" `i) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rotateLeft "rotate_left" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `g
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (termℕ "ℕ")
            "→"
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`j]
           []
           "=>"
           (Algebra.Group.Defs.«term_•_»
            (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
            " • "
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h2)
             ":"
             («term_<_» («term_+_» `m "+" `m) "<" `j)
             "then"
             (num "0")
             "else"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h1)
              ":"
              («term_≤_» `j "≤" `m)
              "then"
              («term_*_»
               (Term.app
                `Quotient.mk'
                [(Term.anonymousCtor
                  "⟨"
                  [(«term_*_» `m "*" `i)
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_*_»
                      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                      "*"
                      («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
                     ","
                     (Term.hole "_")]
                    "⟩")
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                           [])
                          "<;>"
                          (Mathlib.RunCmd.runTac
                           "run_tac"
                           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                  "⟩")])
               "*"
               (Term.app
                `Quotient.mk'
                [(Term.anonymousCtor
                  "⟨"
                  [(«term_*_» `m "*" `i)
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Mathlib.RunCmd.runTac
                          "run_tac"
                          (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                           [])
                          "<;>"
                          (Mathlib.RunCmd.runTac
                           "run_tac"
                           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                  "⟩")]))
              "else"
              («term_*_»
               (Term.app
                `Quotient.mk'
                [(Term.anonymousCtor
                  "⟨"
                  [(«term_*_» `m "*" `i)
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Mathlib.RunCmd.runTac
                          "run_tac"
                          (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                           [])
                          "<;>"
                          (Mathlib.RunCmd.runTac
                           "run_tac"
                           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                  "⟩")])
               "*"
               (Term.app
                `Quotient.mk'
                [(Term.anonymousCtor
                  "⟨"
                  [(«term_*_» `m "*" `i)
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_*_»
                      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                      "*"
                      («term_^_»
                       (Term.app `proj [`𝒜 `i `b])
                       "^"
                       («term_-_» («term_+_» `m "+" `m) "-" `j)))
                     ","
                     (Term.hole "_")]
                    "⟩")
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                           [])
                          "<;>"
                          (Mathlib.RunCmd.runTac
                           "run_tac"
                           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                    "⟩")
                   ","
                   (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
                  "⟩")]))))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j]
        []
        "=>"
        (Algebra.Group.Defs.«term_•_»
         (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
         " • "
         (termDepIfThenElse
          "if"
          (Lean.binderIdent `h2)
          ":"
          («term_<_» («term_+_» `m "+" `m) "<" `j)
          "then"
          (num "0")
          "else"
          (termDepIfThenElse
           "if"
           (Lean.binderIdent `h1)
           ":"
           («term_≤_» `j "≤" `m)
           "then"
           («term_*_»
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(«term_*_» `m "*" `i)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_»
                   («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                   "*"
                   («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
                  ","
                  (Term.hole "_")]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                        [])
                       "<;>"
                       (Mathlib.RunCmd.runTac
                        "run_tac"
                        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
               "⟩")])
            "*"
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(«term_*_» `m "*" `i)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.RunCmd.runTac
                       "run_tac"
                       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                        [])
                       "<;>"
                       (Mathlib.RunCmd.runTac
                        "run_tac"
                        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
               "⟩")]))
           "else"
           («term_*_»
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(«term_*_» `m "*" `i)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.RunCmd.runTac
                       "run_tac"
                       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                        [])
                       "<;>"
                       (Mathlib.RunCmd.runTac
                        "run_tac"
                        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
               "⟩")])
            "*"
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(«term_*_» `m "*" `i)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_»
                   («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                   "*"
                   («term_^_»
                    (Term.app `proj [`𝒜 `i `b])
                    "^"
                    («term_-_» («term_+_» `m "+" `m) "-" `j)))
                  ","
                  (Term.hole "_")]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                        [])
                       "<;>"
                       (Mathlib.RunCmd.runTac
                        "run_tac"
                        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
               "⟩")])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
       " • "
       (termDepIfThenElse
        "if"
        (Lean.binderIdent `h2)
        ":"
        («term_<_» («term_+_» `m "+" `m) "<" `j)
        "then"
        (num "0")
        "else"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h1)
         ":"
         («term_≤_» `j "≤" `m)
         "then"
         («term_*_»
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_*_»
                 («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                 "*"
                 («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
                ","
                (Term.hole "_")]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
             "⟩")])
          "*"
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
             "⟩")]))
         "else"
         («term_*_»
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
             "⟩")])
          "*"
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(«term_*_» `m "*" `i)
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_*_»
                 («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                 "*"
                 («term_^_»
                  (Term.app `proj [`𝒜 `i `b])
                  "^"
                  («term_-_» («term_+_» `m "+" `m) "-" `j)))
                ","
                (Term.hole "_")]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                      [])
                     "<;>"
                     (Mathlib.RunCmd.runTac
                      "run_tac"
                      (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
             "⟩")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h2)
       ":"
       («term_<_» («term_+_» `m "+" `m) "<" `j)
       "then"
       (num "0")
       "else"
       (termDepIfThenElse
        "if"
        (Lean.binderIdent `h1)
        ":"
        («term_≤_» `j "≤" `m)
        "then"
        («term_*_»
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_*_»
                («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
                "*"
                («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
               ","
               (Term.hole "_")]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
            "⟩")])
         "*"
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
            "⟩")]))
        "else"
        («term_*_»
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
            "⟩")])
         "*"
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(«term_*_» `m "*" `i)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_*_»
                («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
                "*"
                («term_^_»
                 (Term.app `proj [`𝒜 `i `b])
                 "^"
                 («term_-_» («term_+_» `m "+" `m) "-" `j)))
               ","
               (Term.hole "_")]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    "<;>"
                    (Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
            "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h1)
       ":"
       («term_≤_» `j "≤" `m)
       "then"
       («term_*_»
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_*_»
               («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
               "*"
               («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
              ","
              (Term.hole "_")]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
           "⟩")])
        "*"
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
           "⟩")]))
       "else"
       («term_*_»
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
           "⟩")])
        "*"
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(«term_*_» `m "*" `i)
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_*_»
               («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
               "*"
               («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
              ","
              (Term.hole "_")]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   "<;>"
                   (Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
          "⟩")])
       "*"
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_*_»
              («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
              "*"
              («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
             ","
             (Term.hole "_")]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.mk'
       [(Term.anonymousCtor
         "⟨"
         [(«term_*_» `m "*" `i)
          ","
          (Term.anonymousCtor
           "⟨"
           [(«term_*_»
             («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
             "*"
             («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
            ","
            (Term.hole "_")]
           "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
                 "<;>"
                 (Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
           "⟩")
          ","
          (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `m "*" `i)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_*_»
           («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
           "*"
           («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
          ","
          (Term.hole "_")]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
               "<;>"
               (Mathlib.RunCmd.runTac
                "run_tac"
                (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
         "⟩")
        ","
        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
             "<;>"
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
           "<;>"
           (Mathlib.RunCmd.runTac
            "run_tac"
            (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
       "<;>"
       (Mathlib.RunCmd.runTac
        "run_tac"
        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_»
         («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
         "*"
         («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
       "*"
       («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» («term_+_» `m "+" `m) "-" `j))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» («term_+_» `m "+" `m) "-" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `m "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_+_» `m "+" `m) "-" `j)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" («term_-_» `j "-" `m))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `j "-" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `j "-" `m) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `Quotient.mk'
       [(Term.anonymousCtor
         "⟨"
         [(«term_*_» `m "*" `i)
          ","
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.RunCmd.runTac
                 "run_tac"
                 (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
           "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
                 "<;>"
                 (Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
           "⟩")
          ","
          (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `m "*" `i)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Mathlib.RunCmd.runTac
               "run_tac"
               (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
               "<;>"
               (Mathlib.RunCmd.runTac
                "run_tac"
                (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
         "⟩")
        ","
        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
             "<;>"
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
           "<;>"
           (Mathlib.RunCmd.runTac
            "run_tac"
            (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
       "<;>"
       (Mathlib.RunCmd.runTac
        "run_tac"
        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.RunCmd.runTac
             "run_tac"
             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.RunCmd.runTac
           "run_tac"
           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_*_»
              («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
              "*"
              («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
             ","
             (Term.hole "_")]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
          "⟩")])
       "*"
       (Term.app
        `Quotient.mk'
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_» `m "*" `i)
           ","
           (Term.anonymousCtor
            "⟨"
            [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  "<;>"
                  (Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
            "⟩")
           ","
           (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.mk'
       [(Term.anonymousCtor
         "⟨"
         [(«term_*_» `m "*" `i)
          ","
          (Term.anonymousCtor
           "⟨"
           [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.RunCmd.runTac
                 "run_tac"
                 (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
           "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
                 "<;>"
                 (Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
           "⟩")
          ","
          (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `m "*" `i)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Mathlib.RunCmd.runTac
               "run_tac"
               (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
               "<;>"
               (Mathlib.RunCmd.runTac
                "run_tac"
                (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
         "⟩")
        ","
        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
             "<;>"
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
           "<;>"
           (Mathlib.RunCmd.runTac
            "run_tac"
            (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
       "<;>"
       (Mathlib.RunCmd.runTac
        "run_tac"
        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.RunCmd.runTac
             "run_tac"
             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.RunCmd.runTac
           "run_tac"
           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `Quotient.mk'
       [(Term.anonymousCtor
         "⟨"
         [(«term_*_» `m "*" `i)
          ","
          (Term.anonymousCtor
           "⟨"
           [(«term_*_»
             («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
             "*"
             («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
            ","
            (Term.hole "_")]
           "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
                 "<;>"
                 (Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
           "⟩")
          ","
          (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `m "*" `i)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_*_»
           («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
           "*"
           («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
          ","
          (Term.hole "_")]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
               "<;>"
               (Mathlib.RunCmd.runTac
                "run_tac"
                (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
         "⟩")
        ","
        (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
             "<;>"
             (Mathlib.RunCmd.runTac
              "run_tac"
              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
           "<;>"
           (Mathlib.RunCmd.runTac
            "run_tac"
            (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
       "<;>"
       (Mathlib.RunCmd.runTac
        "run_tac"
        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_»
         («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
         "*"
         («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
       "*"
       («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `proj [`𝒜 `i `b]) "^" («term_-_» `m "-" `j))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `m "-" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `m "-" `j) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Term.app `proj [`𝒜 `i `a]) "^" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `proj [`𝒜 `i `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `proj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `m "*" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `j "≤" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» («term_+_» `m "+" `m) "<" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» `m "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app (Term.proj («term_+_» `m "+" `m) "." `choose) [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_+_» `m "+" `m) "." `choose)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `m "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `m "+" `m) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (termℕ "ℕ")
       "→"
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
  carrier.add_mem
  ( q : Spec.T A⁰_ f ) { a b : A } ( ha : a ∈ carrier f_deg q ) ( hb : b ∈ carrier f_deg q )
    : a + b ∈ carrier f_deg q
  :=
    by
      refine' fun i => q . 2 . mem_or_mem _ . elim id id
        change ( Quotient.mk' ⟨ _ , _ , _ , _ ⟩ : A⁰_ f ) ∈ q . 1
        ;
        dsimp only [ Subtype.coe_mk ]
        simp_rw [ ← pow_add , map_add , add_pow , mul_comm , ← nsmul_eq_mul ]
        let
          g
            : ℕ → A⁰_ f
            :=
            fun
              j
                =>
                m + m . choose j
                  •
                  if
                    h2
                    :
                    m + m < j
                    then
                    0
                    else
                    if
                      h1
                      :
                      j ≤ m
                      then
                      Quotient.mk'
                          ⟨
                            m * i
                              ,
                              ⟨ proj 𝒜 i a ^ j * proj 𝒜 i b ^ m - j , _ ⟩
                              ,
                              ⟨ _ , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                              ,
                              ⟨ i , rfl ⟩
                            ⟩
                        *
                        Quotient.mk'
                          ⟨
                            m * i
                              ,
                              ⟨ proj 𝒜 i b ^ m , by run_tac mem_tac ⟩
                              ,
                              ⟨ _ , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                              ,
                              ⟨ i , rfl ⟩
                            ⟩
                      else
                      Quotient.mk'
                          ⟨
                            m * i
                              ,
                              ⟨ proj 𝒜 i a ^ m , by run_tac mem_tac ⟩
                              ,
                              ⟨ _ , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                              ,
                              ⟨ i , rfl ⟩
                            ⟩
                        *
                        Quotient.mk'
                          ⟨
                            m * i
                              ,
                              ⟨ proj 𝒜 i a ^ j - m * proj 𝒜 i b ^ m + m - j , _ ⟩
                              ,
                              ⟨ _ , by rw [ mul_comm ] <;> run_tac mem_tac ⟩
                              ,
                              ⟨ i , rfl ⟩
                            ⟩
        rotate_left
        · rw [ ( _ : m * i = _ ) ] run_tac mem_tac rw [ ← add_smul , Nat.add_sub_of_le h1 ] rfl
        ·
          rw [ ( _ : m * i = _ ) ]
            run_tac mem_tac
            rw [ ← add_smul ]
            congr
            zify [ le_of_not_lt h2 , le_of_not_le h1 ]
            abel
        convert_to ∑ i in range m + m + 1 , g i ∈ q . 1
        ;
        swap
        ·
          refine' q . 1 . sum_mem fun j hj => nsmul_mem _ _
            split_ifs
            exacts [ q . 1 . zero_mem , q . 1 . mul_mem_left _ hb i , q . 1 . mul_mem_right _ ha i ]
        rw [ ext_iff_val , val_mk' ]
        change _ = algebraMap HomogeneousLocalization.Away 𝒜 f Localization.Away f _
        dsimp only [ Subtype.coe_mk ]
        ;
        rw [ map_sum , mk_sum ]
        apply Finset.sum_congr rfl fun j hj => _
        change _ = HomogeneousLocalization.val _
        rw [ HomogeneousLocalization.smul_val ]
        split_ifs with h2 h1
        · exact Finset.mem_range . 1 hj . not_le h2 . elim
        all_goals
          simp only [ mul_val , zero_val , val_mk' , Subtype.coe_mk , mk_mul , ← smul_mk ] ; congr 2
        · rw [ mul_assoc , ← pow_add , add_comm m - j , Nat.add_sub_assoc h1 ]
        ;
        · simp_rw [ pow_add ] rfl
        · rw [ ← mul_assoc , ← pow_add , Nat.add_sub_of_le le_of_not_le h1 ]
        ;
        · simp_rw [ pow_add ] rfl
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.add_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.add_mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder "(" [`hm] [":" («term_<_» (num "0") "<" `m)] [] ")")
      (Term.explicitBinder
       "("
       [`q]
       [":"
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
         "Spec.T "
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
       "Spec.T "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termSpec.T_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2382'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable ( hm : 0 < m ) ( q : Spec.T A⁰_ f )

include hm

theorem carrier.zero_mem : (0 : A) ∈ carrier f_deg q := fun i =>
  by
  convert Submodule.zero_mem q.1 using 1
  rw [ext_iff_val, val_mk', zero_val]; simp_rw [map_zero, zero_pow hm]
  convert Localization.mk_zero _ using 1
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.zero_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.3069849967.mem_tac -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `carrier.smul_mem [])
      (Command.declSig
       [(Term.explicitBinder "(" [`c `x] [":" `A] [] ")")
        (Term.explicitBinder
         "("
         [`hx]
         [":" («term_∈_» `x "∈" (Term.app `carrier [`f_deg `q]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» (Algebra.Group.Defs.«term_•_» `c " • " `x) "∈" (Term.app `carrier [`f_deg `q]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.revert "revert" [`c])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `DirectSum.Decomposition.induction_on
             [`𝒜 (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]") [])
             []
             (Tactic.exact "exact" (Term.app `carrier.zero_mem [`f_deg `hm (Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
              [])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Subtype.coe_mk)
                ","
                (Tactic.rwRule [] `proj_apply)
                ","
                (Tactic.rwRule [] `smul_eq_mul)
                ","
                (Tactic.rwRule [] (Term.app `coe_decompose_mul_of_left_mem [`𝒜 `i `ha]))]
               "]")
              [])
             []
             (Mathlib.Tactic.splitIfs "split_ifs" [] [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(convertTo
                "convert_to"
                («term_∈_»
                 (Term.typeAscription
                  "("
                  («term_*_»
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.hole "_")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
                      "⟩")])
                   "*"
                   (Term.app
                    `Quotient.mk'
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.hole "_")
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Mathlib.RunCmd.runTac
                              "run_tac"
                              (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                        "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                       ","
                       (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
                      "⟩")]))
                  ":"
                  [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»
                    "A⁰_ "
                    `f)]
                  ")")
                 "∈"
                 (Term.proj `q "." (fieldIdx "1")))
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `ext_iff_val)
                    ","
                    (Tactic.rwRule [] `val_mk')
                    ","
                    (Tactic.rwRule [] `mul_val)
                    ","
                    (Tactic.rwRule [] `val_mk')
                    ","
                    (Tactic.rwRule [] `val_mk')
                    ","
                    (Tactic.rwRule [] `Subtype.coe_mk)]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
                   "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]")
                  [])
                 []
                 (Tactic.congr "congr" [])
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
                    ","
                    (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
                   "]")
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact
                  "exact"
                  (Term.app
                   `Ideal.mul_mem_left
                   [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)]
                   "]")
                  [])
                 []
                 (Mathlib.RunCmd.runTac
                  "run_tac"
                  (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_pow [`hm]))] "]")
                [])
               []
               (convert "convert" [] (Term.app `carrier.zero_mem [`f_deg `hm `q `i]) [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `map_zero) "," (Tactic.rwRule [] (Term.app `zero_pow [`hm]))]
                 "]")
                [])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_smul)] "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.hole "_") (Term.hole "_")]
                []
                "=>"
                (Term.app `carrier.add_mem [`f_deg `q]))))])])))
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
         [(Tactic.revert "revert" [`c])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `DirectSum.Decomposition.induction_on
            [`𝒜 (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]") [])
            []
            (Tactic.exact "exact" (Term.app `carrier.zero_mem [`f_deg `hm (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `proj_apply)
               ","
               (Tactic.rwRule [] `smul_eq_mul)
               ","
               (Tactic.rwRule [] (Term.app `coe_decompose_mul_of_left_mem [`𝒜 `i `ha]))]
              "]")
             [])
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(convertTo
               "convert_to"
               («term_∈_»
                (Term.typeAscription
                 "("
                 («term_*_»
                  (Term.app
                   `Quotient.mk'
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.hole "_")
                      ","
                      (Term.anonymousCtor
                       "⟨"
                       [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
                       "⟩")
                      ","
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                      ","
                      (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
                     "⟩")])
                  "*"
                  (Term.app
                   `Quotient.mk'
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.hole "_")
                      ","
                      (Term.anonymousCtor
                       "⟨"
                       [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
                        ","
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Mathlib.RunCmd.runTac
                             "run_tac"
                             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                       "⟩")
                      ","
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                      ","
                      (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
                     "⟩")]))
                 ":"
                 [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»
                   "A⁰_ "
                   `f)]
                 ")")
                "∈"
                (Term.proj `q "." (fieldIdx "1")))
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `ext_iff_val)
                   ","
                   (Tactic.rwRule [] `val_mk')
                   ","
                   (Tactic.rwRule [] `mul_val)
                   ","
                   (Tactic.rwRule [] `val_mk')
                   ","
                   (Tactic.rwRule [] `val_mk')
                   ","
                   (Tactic.rwRule [] `Subtype.coe_mk)]
                  "]")
                 [])
                []
                (Mathlib.Tactic.tacticSimp_rw__
                 "simp_rw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
                  "]")
                 [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]")
                 [])
                []
                (Tactic.congr "congr" [])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
                   ","
                   (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
                  "]")
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.app
                  `Ideal.mul_mem_left
                  [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)]
                  "]")
                 [])
                []
                (Mathlib.RunCmd.runTac
                 "run_tac"
                 (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_pow [`hm]))] "]")
               [])
              []
              (convert "convert" [] (Term.app `carrier.zero_mem [`f_deg `hm `q `i]) [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `map_zero) "," (Tactic.rwRule [] (Term.app `zero_pow [`hm]))]
                "]")
               [])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_smul)] "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_") (Term.hole "_")]
               []
               "=>"
               (Term.app `carrier.add_mem [`f_deg `q]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_smul)] "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_") (Term.hole "_")]
           []
           "=>"
           (Term.app `carrier.add_mem [`f_deg `q]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.hole "_") (Term.hole "_")]
         []
         "=>"
         (Term.app `carrier.add_mem [`f_deg `q]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.app `carrier.add_mem [`f_deg `q])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.add_mem [`f_deg `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.add_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_smul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
              [])]
            "⟩"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
         [])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Subtype.coe_mk)
           ","
           (Tactic.rwRule [] `proj_apply)
           ","
           (Tactic.rwRule [] `smul_eq_mul)
           ","
           (Tactic.rwRule [] (Term.app `coe_decompose_mul_of_left_mem [`𝒜 `i `ha]))]
          "]")
         [])
        []
        (Mathlib.Tactic.splitIfs "split_ifs" [] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(convertTo
           "convert_to"
           («term_∈_»
            (Term.typeAscription
             "("
             («term_*_»
              (Term.app
               `Quotient.mk'
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
                   "⟩")
                  ","
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                  ","
                  (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
                 "⟩")])
              "*"
              (Term.app
               `Quotient.mk'
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Mathlib.RunCmd.runTac
                         "run_tac"
                         (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                   "⟩")
                  ","
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                  ","
                  (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
                 "⟩")]))
             ":"
             [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
             ")")
            "∈"
            (Term.proj `q "." (fieldIdx "1")))
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `ext_iff_val)
               ","
               (Tactic.rwRule [] `val_mk')
               ","
               (Tactic.rwRule [] `mul_val)
               ","
               (Tactic.rwRule [] `val_mk')
               ","
               (Tactic.rwRule [] `val_mk')
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)]
              "]")
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
              "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]")
             [])
            []
            (Tactic.congr "congr" [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
               ","
               (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `Ideal.mul_mem_left
              [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)]
              "]")
             [])
            []
            (Mathlib.RunCmd.runTac
             "run_tac"
             (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_pow [`hm]))] "]")
           [])
          []
          (convert "convert" [] (Term.app `carrier.zero_mem [`f_deg `hm `q `i]) [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `map_zero) "," (Tactic.rwRule [] (Term.app `zero_pow [`hm]))]
            "]")
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_pow [`hm]))] "]")
         [])
        []
        (convert "convert" [] (Term.app `carrier.zero_mem [`f_deg `hm `q `i]) [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `map_zero) "," (Tactic.rwRule [] (Term.app `zero_pow [`hm]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_zero) "," (Tactic.rwRule [] (Term.app `zero_pow [`hm]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_pow [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `carrier.zero_mem [`f_deg `hm `q `i]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.zero_mem [`f_deg `hm `q `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_pow [`hm]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_pow [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(convertTo
         "convert_to"
         («term_∈_»
          (Term.typeAscription
           "("
           («term_*_»
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                ","
                (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
               "⟩")])
            "*"
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.RunCmd.runTac
                       "run_tac"
                       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                ","
                (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
               "⟩")]))
           ":"
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
           ")")
          "∈"
          (Term.proj `q "." (fieldIdx "1")))
         [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `ext_iff_val)
             ","
             (Tactic.rwRule [] `val_mk')
             ","
             (Tactic.rwRule [] `mul_val)
             ","
             (Tactic.rwRule [] `val_mk')
             ","
             (Tactic.rwRule [] `val_mk')
             ","
             (Tactic.rwRule [] `Subtype.coe_mk)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]")
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
             ","
             (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
            "]")
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.app
            `Ideal.mul_mem_left
            [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)]
            "]")
           [])
          []
          (Mathlib.RunCmd.runTac
           "run_tac"
           (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `Ideal.mul_mem_left
          [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)]
          "]")
         [])
        []
        (Mathlib.RunCmd.runTac
         "run_tac"
         (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.RunCmd.runTac
       "run_tac"
       (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_tac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_eq_mul) "," (Tactic.rwRule [] `mul_comm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Ideal.mul_mem_left
        [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mul_mem_left
       [(Term.hole "_") (Term.hole "_") (Term.app `hx [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hx [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hx [(Term.hole "_")]) ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `ext_iff_val)
           ","
           (Tactic.rwRule [] `val_mk')
           ","
           (Tactic.rwRule [] `mul_val)
           ","
           (Tactic.rwRule [] `val_mk')
           ","
           (Tactic.rwRule [] `val_mk')
           ","
           (Tactic.rwRule [] `Subtype.coe_mk)]
          "]")
         [])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
          "]")
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]")
         [])
        []
        (Tactic.congr "congr" [])
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
           ","
           (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_of_le [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Localization.mk_mul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_pow) "," (Tactic.rwRule [] `Subtype.coe_mk)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `ext_iff_val)
         ","
         (Tactic.rwRule [] `val_mk')
         ","
         (Tactic.rwRule [] `mul_val)
         ","
         (Tactic.rwRule [] `val_mk')
         ","
         (Tactic.rwRule [] `val_mk')
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convertTo
       "convert_to"
       («term_∈_»
        (Term.typeAscription
         "("
         («term_*_»
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
              ","
              (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
             "⟩")])
          "*"
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.anonymousCtor
               "⟨"
               [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
               "⟩")
              ","
              (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
              ","
              (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
             "⟩")]))
         ":"
         [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
         ")")
        "∈"
        (Term.proj `q "." (fieldIdx "1")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription
        "("
        («term_*_»
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
             ","
             (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
            "⟩")])
         "*"
         (Term.app
          `Quotient.mk'
          [(Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.RunCmd.runTac
                    "run_tac"
                    (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
             ","
             (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
            "⟩")]))
        ":"
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
        ")")
       "∈"
       (Term.proj `q "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `q "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       («term_*_»
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» `a "^" `m) "," (Term.app `pow_mem_graded [`m `ha])]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
            ","
            (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]
           "⟩")])
        "*"
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.anonymousCtor
             "⟨"
             [(«term_^_» (Term.app `proj [`𝒜 («term_-_» `i "-" `n) `x]) "^" `m)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.RunCmd.runTac
                   "run_tac"
                   (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `mem_tac) [])]))])))]
             "⟩")
            ","
            (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
            ","
            (Term.anonymousCtor "⟨" [(«term_-_» `i "-" `n) "," `rfl] "⟩")]
           "⟩")]))
       ":"
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termA⁰__._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.2426'
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
  carrier.smul_mem
  ( c x : A ) ( hx : x ∈ carrier f_deg q ) : c • x ∈ carrier f_deg q
  :=
    by
      revert c
        refine' DirectSum.Decomposition.induction_on 𝒜 _ _ _
        · rw [ zero_smul ] exact carrier.zero_mem f_deg hm _
        ·
          rintro n ⟨ a , ha ⟩ i
            simp_rw
              [ Subtype.coe_mk , proj_apply , smul_eq_mul , coe_decompose_mul_of_left_mem 𝒜 i ha ]
            split_ifs
            ·
              convert_to
                  (
                      Quotient.mk' ⟨ _ , ⟨ a ^ m , pow_mem_graded m ha ⟩ , ⟨ _ , _ ⟩ , ⟨ n , rfl ⟩ ⟩
                        *
                        Quotient.mk'
                          ⟨
                            _
                              ,
                              ⟨ proj 𝒜 i - n x ^ m , by run_tac mem_tac ⟩
                              ,
                              ⟨ _ , _ ⟩
                              ,
                              ⟨ i - n , rfl ⟩
                            ⟩
                      :
                      A⁰_ f
                      )
                    ∈
                    q . 1
                ·
                  erw [ ext_iff_val , val_mk' , mul_val , val_mk' , val_mk' , Subtype.coe_mk ]
                    simp_rw [ mul_pow , Subtype.coe_mk ]
                    rw [ Localization.mk_mul ]
                    congr
                    erw [ ← pow_add , Nat.add_sub_of_le h ]
                · exact Ideal.mul_mem_left _ _ hx _ rw [ smul_eq_mul , mul_comm ] run_tac mem_tac
            ·
              simp_rw [ zero_pow hm ]
                convert carrier.zero_mem f_deg hm q i
                rw [ map_zero , zero_pow hm ]
        · simp_rw [ add_smul ] exact fun _ _ => carrier.add_mem f_deg q
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.smul_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.smul_mem

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
def carrier.asIdeal : Ideal A where
  carrier := carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' a b := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal

theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 :=
  fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h =>
    by
    simp only [proj_apply, decompose_of_mem_ne 𝒜 (Submodule.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm]
    convert carrier.zero_mem f_deg hm q j; rw [map_zero, zero_pow hm]
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ideal.
-/
def carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_homogeneous_ideal AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal

theorem carrier.denom_not_mem : f ∉ carrier.asIdeal f_deg hm q := fun rid =>
  q.IsPrime.ne_top <|
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        simpa only [ext_iff_val, one_val, proj_apply, decompose_of_mem_same _ f_deg, val_mk'] using
          (mk_self (⟨_, m, rfl⟩ : Submonoid.powers f)).symm)
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.denom_not_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.denom_not_mem

theorem carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ carrier.asHomogeneousIdeal f_deg hm q :=
  fun rid => carrier.denom_not_mem f_deg hm q <| rid <| DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.relevant AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.relevant

theorem carrier.asIdeal.ne_top : carrier.asIdeal f_deg hm q ≠ ⊤ := fun rid =>
  carrier.denom_not_mem f_deg hm q (rid.symm ▸ Submodule.mem_top)
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.ne_top AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.ne_top

theorem carrier.asIdeal.prime : (carrier.asIdeal f_deg hm q).IsPrime :=
  ((carrier.asIdeal.homogeneous f_deg hm q).isPrimeOfHomogeneousMemOrMem
      (carrier.asIdeal.ne_top f_deg hm q))
    fun x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (∀ i, _ ∈ _) ∨ ∀ i, _ ∈ _
      by
      rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left]
      · apply q.2.mem_or_mem
        convert hxy (nx + ny) using 1
        simp_rw [proj_apply, decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (mul_mem hnx hny), mul_pow, pow_add]
        simpa only [ext_iff_val, val_mk', mul_val, mk_mul]
      all_goals
        intro n hn; convert q.1.zero_mem using 1
        rw [ext_iff_val, val_mk', zero_val]; simp_rw [proj_apply, Subtype.coe_mk]
        convert mk_zero _; rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm]
        · first |exact hnx|exact hny
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.prime AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime

variable (f_deg)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toFun [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
           "Spec.T "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
          "→"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»
           "Proj.T| "
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`q]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.app `carrier.asHomogeneousIdeal [`f_deg `hm `q])
             ","
             (Term.app `carrier.asIdeal.prime [`f_deg `hm `q])
             ","
             (Term.app `carrier.relevant [`f_deg `hm `q])]
            "⟩")
           ","
           («term_<|_»
            (Term.proj
             (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
             "."
             `mp)
            "<|"
            (Term.app `carrier.denom_not_mem [`f_deg `hm `q]))]
          "⟩")))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`q]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.app `carrier.asHomogeneousIdeal [`f_deg `hm `q])
            ","
            (Term.app `carrier.asIdeal.prime [`f_deg `hm `q])
            ","
            (Term.app `carrier.relevant [`f_deg `hm `q])]
           "⟩")
          ","
          («term_<|_»
           (Term.proj
            (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
            "."
            `mp)
           "<|"
           (Term.app `carrier.denom_not_mem [`f_deg `hm `q]))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.app `carrier.asHomogeneousIdeal [`f_deg `hm `q])
          ","
          (Term.app `carrier.asIdeal.prime [`f_deg `hm `q])
          ","
          (Term.app `carrier.relevant [`f_deg `hm `q])]
         "⟩")
        ","
        («term_<|_»
         (Term.proj
          (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
          "."
          `mp)
         "<|"
         (Term.app `carrier.denom_not_mem [`f_deg `hm `q]))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
        "."
        `mp)
       "<|"
       (Term.app `carrier.denom_not_mem [`f_deg `hm `q]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.denom_not_mem [`f_deg `hm `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.denom_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
       "."
       `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjectiveSpectrum.mem_basic_open [(Term.hole "_") `f (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `carrier.asHomogeneousIdeal [`f_deg `hm `q])
        ","
        (Term.app `carrier.asIdeal.prime [`f_deg `hm `q])
        ","
        (Term.app `carrier.relevant [`f_deg `hm `q])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.relevant [`f_deg `hm `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.relevant
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.asIdeal.prime [`f_deg `hm `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.asIdeal.prime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `carrier.asHomogeneousIdeal [`f_deg `hm `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f_deg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `carrier.asHomogeneousIdeal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termSpec.T_»
        "Spec.T "
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termA⁰__» "A⁰_ " `f))
       "→"
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»
        "Proj.T| "
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»
       "Proj.T| "
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termpbo_ "pbo " `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.«termProj.T|_»', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.Scheme.termProj.T|_._@.AlgebraicGeometry.ProjectiveSpectrum.Scheme._hyg.593'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
    -/
  def
    toFun
    : Spec.T A⁰_ f → Proj.T| pbo f
    :=
      fun
        q
          =>
          ⟨
            ⟨
                carrier.asHomogeneousIdeal f_deg hm q
                  ,
                  carrier.asIdeal.prime f_deg hm q
                  ,
                  carrier.relevant f_deg hm q
                ⟩
              ,
              ProjectiveSpectrum.mem_basic_open _ f _ . mp <| carrier.denom_not_mem f_deg hm q
            ⟩
#align
  algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.toFun

end FromSpec

end ProjIsoSpecTopComponent

end AlgebraicGeometry

