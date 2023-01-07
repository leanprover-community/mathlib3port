/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebraic_geometry.projective_spectrum.structure_sheaf
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathbin.Topology.Sheaves.LocalPredicate
import Mathbin.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathbin.AlgebraicGeometry.LocallyRingedSpace

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `src/algebraic_geometry/topology.lean`, we have given a topology on `projective_spectrum 𝒜`; in
this file we will construct a sheaf on `projective_spectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `projective_spectrum.Top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, homogeneous_localization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, homogeneous_localization 𝒜 x`.
* `algebraic_geometry.Proj.structure_sheaf`: the sheaf with `U ↦ sections_subring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `algebraic_geometry.Proj.stalk_iso'`: for any `x : projective_spectrum 𝒜`, the stalk of
  `Proj.structure_sheaf` at `x` is isomorphic to `homogeneous_localization 𝒜 x`.
* `algebraic_geometry.Proj.to_LocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

namespace AlgebraicGeometry

open DirectSum BigOperators Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {R A : Type _}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

-- mathport name: «exprat »
local notation "at " x => HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal

namespace ProjectiveSpectrum.StructureSheaf

variable {𝒜}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The predicate saying that a dependent function on an open `U` is realised as a fixed fraction\n`r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `IsFraction [])
      (Command.optDeclSig
       [(Term.implicitBinder
         "{"
         [`U]
         [":" (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])]
         "}")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" `U)]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (termℕ "ℕ") ")")
          (Lean.bracketedExplicitBinders
           "("
           [(Lean.binderIdent `r) (Lean.binderIdent `s)]
           ":"
           (Term.app `𝒜 [`i])
           ")")])
        ","
        (Term.forall
         "∀"
         [`x]
         [(Term.typeSpec ":" `U)]
         ","
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `s_nin)]
            [":"
             («term_∉_»
              (Term.proj `s "." (fieldIdx "1"))
              "∉"
              (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))]))
          ","
          («term_=_»
           (Term.app `f [`x])
           "="
           (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")])))))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (termℕ "ℕ") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `r) (Lean.binderIdent `s)]
          ":"
          (Term.app `𝒜 [`i])
          ")")])
       ","
       (Term.forall
        "∀"
        [`x]
        [(Term.typeSpec ":" `U)]
        ","
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `s_nin)]
           [":"
            («term_∉_»
             (Term.proj `s "." (fieldIdx "1"))
             "∉"
             (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))]))
         ","
         («term_=_»
          (Term.app `f [`x])
          "="
          (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" `U)]
       ","
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `s_nin)]
          [":"
           («term_∉_»
            (Term.proj `s "." (fieldIdx "1"))
            "∉"
            (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))]))
        ","
        («term_=_»
         (Term.app `f [`x])
         "="
         (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `s_nin)]
         [":"
          («term_∉_»
           (Term.proj `s "." (fieldIdx "1"))
           "∉"
           (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))]))
       ","
       («term_=_»
        (Term.app `f [`x])
        "="
        (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `f [`x])
       "="
       (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quotient.mk' [(Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `r "," `s "," `s_nin] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s_nin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∉_»
       (Term.proj `s "." (fieldIdx "1"))
       "∉"
       (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." (fieldIdx "1")) "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `𝒜 [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" `U)]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
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
    The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
    `r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).
    -/
  def
    IsFraction
    { U : Opens ProjectiveSpectrum.top 𝒜 } ( f : ∀ x : U , at x . 1 ) : Prop
    :=
      ∃
        ( i : ℕ ) ( r s : 𝒜 i )
        ,
        ∀
          x
          : U
          ,
          ∃ s_nin : s . 1 ∉ x . 1 . asHomogeneousIdeal , f x = Quotient.mk' ⟨ i , r , s , s_nin ⟩
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.IsFraction

variable (𝒜)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The predicate `is_fraction` is \"prelocal\", in the sense that if it holds on `U` it holds on any open\nsubset `V` of `U`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `isFractionPrelocal [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `PrelocalPredicate
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
             "=>"
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
              "at "
              `x)))]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `pred [`U `f] [] ":=" (Term.app `IsFraction [`f]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `res
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Std.Tactic.rintro
                 "rintro"
                 [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `V))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `U))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))
                  (Std.Tactic.RCases.rintroPat.one
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
                      [])]
                    "⟩"))]
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [`j
                   ","
                   `r
                   ","
                   `s
                   ","
                   (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))]
                  "⟩")))]))))))]
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
         [(Tactic.«tactic_<;>_»
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `V))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `U))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
                 [])]
               "⟩"))]
            [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [`j
              ","
              `r
              ","
              `s
              ","
              (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))]
             "⟩")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.rintro
        "rintro"
        [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `V))
         (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `U))
         (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
         (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))
         (Std.Tactic.RCases.rintroPat.one
          (Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
             [])]
           "⟩"))]
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [`j
          ","
          `r
          ","
          `s
          ","
          (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`j
         ","
         `r
         ","
         `s
         ","
         (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`j
        ","
        `r
        ","
        `s
        ","
        (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `w [(Term.app `i [`y])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `w [(Term.app `i [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i [`y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `w
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `V))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `U))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsFraction [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PrelocalPredicate
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
          "=>"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
           "at "
           `x)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
        "=>"
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The predicate `is_fraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
    subset `V` of `U`.
    -/
  def
    isFractionPrelocal
    : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x
    where
      pred U f := IsFraction f
        res := by rintro V U i f ⟨ j , r , s , w ⟩ <;> exact ⟨ j , r , s , fun y => w i y ⟩
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction_prelocal AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isFractionPrelocal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "We will define the structure sheaf as the subsheaf of all dependent functions in\n`Π x : U, homogeneous_localization 𝒜 x` consisting of those functions which can locally be expressed\nas a ratio of `A` of same grading.-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `isLocallyFraction [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `LocalPredicate
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
             "=>"
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
              "at "
              `x)))]))])
      (Command.declValSimple ":=" (Term.proj (Term.app `isFractionPrelocal [`𝒜]) "." `sheafify) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `isFractionPrelocal [`𝒜]) "." `sheafify)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isFractionPrelocal [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isFractionPrelocal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isFractionPrelocal [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `LocalPredicate
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
          "=>"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
           "at "
           `x)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" (Term.app `ProjectiveSpectrum.top [`𝒜]))]
        "=>"
        (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    We will define the structure sheaf as the subsheaf of all dependent functions in
    `Π x : U, homogeneous_localization 𝒜 x` consisting of those functions which can locally be expressed
    as a ratio of `A` of same grading.-/
  def
    isLocallyFraction
    : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x
    := isFractionPrelocal 𝒜 . sheafify
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `zero_mem' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Term.forall
             "∀"
             [`x]
             [(Term.typeSpec ":" (Term.app `unop [`U]))]
             ","
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
              "at "
              (Term.proj `x "." (fieldIdx "1"))))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `unop [`U])
           ","
           (Term.proj `x "." (fieldIdx "2"))
           ","
           (Term.app
            (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
            [(Term.app `unop [`U])])
           ","
           (Term.anonymousCtor
            "⟨"
            [(num "0")
             ","
             (Term.anonymousCtor "⟨" [(num "0") "," (Term.app `zero_mem [(Term.hole "_")])] "⟩")
             ","
             (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
             ","
             (Term.fun
              "fun"
              (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
            "⟩")]
          "⟩")))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `unop [`U])
          ","
          (Term.proj `x "." (fieldIdx "2"))
          ","
          (Term.app
           (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
           [(Term.app `unop [`U])])
          ","
          (Term.anonymousCtor
           "⟨"
           [(num "0")
            ","
            (Term.anonymousCtor "⟨" [(num "0") "," (Term.app `zero_mem [(Term.hole "_")])] "⟩")
            ","
            (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
            ","
            (Term.fun
             "fun"
             (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
           "⟩")]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `unop [`U])
        ","
        (Term.proj `x "." (fieldIdx "2"))
        ","
        (Term.app
         (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
         [(Term.app `unop [`U])])
        ","
        (Term.anonymousCtor
         "⟨"
         [(num "0")
          ","
          (Term.anonymousCtor "⟨" [(num "0") "," (Term.app `zero_mem [(Term.hole "_")])] "⟩")
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
          ","
          (Term.fun
           "fun"
           (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (Term.anonymousCtor "⟨" [(num "0") "," (Term.app `zero_mem [(Term.hole "_")])] "⟩")
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "0") "," (Term.app `zero_mem [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_mem [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `unop [`U])])
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
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" (Term.app `unop [`U]))]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Term.forall
         "∀"
         [`x]
         [(Term.typeSpec ":" (Term.app `unop [`U]))]
         ","
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
          "at "
          (Term.proj `x "." (fieldIdx "1"))))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  zero_mem'
  ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ )
    : isLocallyFraction 𝒜 . pred ( 0 : ∀ x : unop U , at x . 1 )
  :=
    fun
      x
        =>
        ⟨
          unop U
            ,
            x . 2
            ,
            𝟙 unop U
            ,
            ⟨ 0 , ⟨ 0 , zero_mem _ ⟩ , ⟨ 1 , one_mem ⟩ , fun y => ⟨ _ , rfl ⟩ ⟩
          ⟩
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.zero_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.zero_mem'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `one_mem' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
         [(Term.typeAscription
           "("
           (num "1")
           ":"
           [(Term.forall
             "∀"
             [`x]
             [(Term.typeSpec ":" (Term.app `unop [`U]))]
             ","
             (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
              "at "
              (Term.proj `x "." (fieldIdx "1"))))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `unop [`U])
           ","
           (Term.proj `x "." (fieldIdx "2"))
           ","
           (Term.app
            (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
            [(Term.app `unop [`U])])
           ","
           (Term.anonymousCtor
            "⟨"
            [(num "0")
             ","
             (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
             ","
             (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
             ","
             (Term.fun
              "fun"
              (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
            "⟩")]
          "⟩")))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `unop [`U])
          ","
          (Term.proj `x "." (fieldIdx "2"))
          ","
          (Term.app
           (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
           [(Term.app `unop [`U])])
          ","
          (Term.anonymousCtor
           "⟨"
           [(num "0")
            ","
            (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
            ","
            (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
            ","
            (Term.fun
             "fun"
             (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
           "⟩")]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `unop [`U])
        ","
        (Term.proj `x "." (fieldIdx "2"))
        ","
        (Term.app
         (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
         [(Term.app `unop [`U])])
        ","
        (Term.anonymousCtor
         "⟨"
         [(num "0")
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
          ","
          (Term.fun
           "fun"
           (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`y] [] "=>" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," `one_mem] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `unop [`U])])
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
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
       [(Term.typeAscription
         "("
         (num "1")
         ":"
         [(Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" (Term.app `unop [`U]))]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "1")
       ":"
       [(Term.forall
         "∀"
         [`x]
         [(Term.typeSpec ":" (Term.app `unop [`U]))]
         ","
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
          "at "
          (Term.proj `x "." (fieldIdx "1"))))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  one_mem'
  ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ )
    : isLocallyFraction 𝒜 . pred ( 1 : ∀ x : unop U , at x . 1 )
  :=
    fun
      x
        =>
        ⟨
          unop U
            ,
            x . 2
            ,
            𝟙 unop U
            ,
            ⟨ 0 , ⟨ 1 , one_mem ⟩ , ⟨ 1 , one_mem ⟩ , fun y => ⟨ _ , rfl ⟩ ⟩
          ⟩
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.one_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.one_mem'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_mem' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`a `b]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" (Term.app `unop [`U]))]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha]
         [":" (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hb]
         [":" (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`b])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
         [(«term_+_» `a "+" `b)])))
      (Command.declValSimple
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
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `ha [`x]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hb [`x]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
                ","
                (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
                ","
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 `ia)
                ","
                («term_+_» `ja "+" `jb)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
                  ","
                  (Term.app
                   `add_mem
                   [(Term.typeAscription
                     "("
                     (Term.subst
                      (Term.app `add_comm [`jb `ja])
                      "▸"
                      [(Term.app `mul_mem [`sb_mem `ra_mem])])
                     ":"
                     [(«term_∈_»
                       («term_*_» `sb "*" `ra)
                       "∈"
                       (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
                     ")")
                    (Term.app `mul_mem [`sa_mem `rb_mem])])]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
                 "⟩")
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`y]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                    ","
                    (Term.hole "_")]
                   "⟩")))]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.cases'
                "cases'"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   (Term.proj
                    (Term.proj
                     (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                     "."
                     `IsPrime)
                    "."
                    `mem_or_mem)
                   [`h]))]
                []
                ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     `wa
                     [(Term.anonymousCtor
                       "⟨"
                       [`y
                        ","
                        (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                       "⟩")])]])
                 []
                 (Tactic.exact "exact" (Term.app `nin [`h]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     `wb
                     [(Term.anonymousCtor
                       "⟨"
                       [`y
                        ","
                        (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                       "⟩")])]])
                 []
                 (Tactic.exact "exact" (Term.app `nin [`h]))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `add_mul)
                  ","
                  (Tactic.simpLemma [] [] `map_add)
                  ","
                  (Tactic.simpLemma [] [] `Pi.add_apply)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.map_mul)
                  ","
                  (Tactic.simpLemma [] [] `ext_iff_val)
                  ","
                  (Tactic.simpLemma [] [] `add_val)]
                 "]"]
                [])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin1)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])]])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin2)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])]])
               []
               (Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                []
                [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)] "]")
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
                   [(Tactic.simpLemma [] [] `val_mk')
                    ","
                    (Tactic.simpLemma [] [] `add_mk)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                    ","
                    (Tactic.simpLemma [] [] `add_comm)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `mul_comm [`sa `sb]))]
                   "]")]
                 []))])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
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
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `ha [`x]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hb [`x]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
               ","
               (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
               ","
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                `ia)
               ","
               («term_+_» `ja "+" `jb)
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
                 ","
                 (Term.app
                  `add_mem
                  [(Term.typeAscription
                    "("
                    (Term.subst
                     (Term.app `add_comm [`jb `ja])
                     "▸"
                     [(Term.app `mul_mem [`sb_mem `ra_mem])])
                    ":"
                    [(«term_∈_»
                      («term_*_» `sb "*" `ra)
                      "∈"
                      (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
                    ")")
                   (Term.app `mul_mem [`sa_mem `rb_mem])])]
                "⟩")
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
                "⟩")
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`y]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                   ","
                   (Term.hole "_")]
                  "⟩")))]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.cases'
               "cases'"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                    "."
                    `IsPrime)
                   "."
                   `mem_or_mem)
                  [`h]))]
               []
               ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    `wa
                    [(Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                      "⟩")])]])
                []
                (Tactic.exact "exact" (Term.app `nin [`h]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    `wb
                    [(Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                      "⟩")])]])
                []
                (Tactic.exact "exact" (Term.app `nin [`h]))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `add_mul)
                 ","
                 (Tactic.simpLemma [] [] `map_add)
                 ","
                 (Tactic.simpLemma [] [] `Pi.add_apply)
                 ","
                 (Tactic.simpLemma [] [] `RingHom.map_mul)
                 ","
                 (Tactic.simpLemma [] [] `ext_iff_val)
                 ","
                 (Tactic.simpLemma [] [] `add_val)]
                "]"]
               [])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])]])
              []
              (Tactic.dsimp
               "dsimp"
               []
               []
               ["only"]
               []
               [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)] "]")
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
                  [(Tactic.simpLemma [] [] `val_mk')
                   ","
                   (Tactic.simpLemma [] [] `add_mk)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                   ","
                   (Tactic.simpLemma [] [] `add_comm)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `mul_comm [`sa `sb]))]
                  "]")]
                []))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `ha [`x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `hb [`x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
             ","
             (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
             ","
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              `ia)
             ","
             («term_+_» `ja "+" `jb)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
               ","
               (Term.app
                `add_mem
                [(Term.typeAscription
                  "("
                  (Term.subst
                   (Term.app `add_comm [`jb `ja])
                   "▸"
                   [(Term.app `mul_mem [`sb_mem `ra_mem])])
                  ":"
                  [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
                  ")")
                 (Term.app `mul_mem [`sa_mem `rb_mem])])]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
              "⟩")
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
                "⟩")))]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.cases'
             "cases'"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                  "."
                  `IsPrime)
                 "."
                 `mem_or_mem)
                [`h]))]
             []
             ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  `wa
                  [(Term.anonymousCtor
                    "⟨"
                    [`y
                     ","
                     (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                    "⟩")])]])
              []
              (Tactic.exact "exact" (Term.app `nin [`h]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  `wb
                  [(Term.anonymousCtor
                    "⟨"
                    [`y
                     ","
                     (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                    "⟩")])]])
              []
              (Tactic.exact "exact" (Term.app `nin [`h]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `add_mul)
               ","
               (Tactic.simpLemma [] [] `map_add)
               ","
               (Tactic.simpLemma [] [] `Pi.add_apply)
               ","
               (Tactic.simpLemma [] [] `RingHom.map_mul)
               ","
               (Tactic.simpLemma [] [] `ext_iff_val)
               ","
               (Tactic.simpLemma [] [] `add_val)]
              "]"]
             [])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])]])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)] "]")
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
                [(Tactic.simpLemma [] [] `val_mk')
                 ","
                 (Tactic.simpLemma [] [] `add_mk)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                 ","
                 (Tactic.simpLemma [] [] `add_comm)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `mul_comm [`sa `sb]))]
                "]")]
              []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `add_mul)
           ","
           (Tactic.simpLemma [] [] `map_add)
           ","
           (Tactic.simpLemma [] [] `Pi.add_apply)
           ","
           (Tactic.simpLemma [] [] `RingHom.map_mul)
           ","
           (Tactic.simpLemma [] [] `ext_iff_val)
           ","
           (Tactic.simpLemma [] [] `add_val)]
          "]"]
         [])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin1)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])]])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin2)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])]])
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         []
         [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] []))])
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)] "]")
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
            [(Tactic.simpLemma [] [] `val_mk')
             ","
             (Tactic.simpLemma [] [] `add_mk)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `add_comm)
             ","
             (Tactic.simpLemma [] [] (Term.app `mul_comm [`sa `sb]))]
            "]")]
          []))])
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
          [(Tactic.simpLemma [] [] `val_mk')
           ","
           (Tactic.simpLemma [] [] `add_mk)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
           ","
           (Tactic.simpLemma [] [] `add_comm)
           ","
           (Tactic.simpLemma [] [] (Term.app `mul_comm [`sa `sb]))]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [`sa `sb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sa
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
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
      `add_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       []
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy2)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy1)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_left [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_left [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wa
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
        [(Tactic.simpLemma [] [] `add_mul)
         ","
         (Tactic.simpLemma [] [] `map_add)
         ","
         (Tactic.simpLemma [] [] `Pi.add_apply)
         ","
         (Tactic.simpLemma [] [] `RingHom.map_mul)
         ","
         (Tactic.simpLemma [] [] `ext_iff_val)
         ","
         (Tactic.simpLemma [] [] `add_val)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.proj
              (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
              "."
              `IsPrime)
             "."
             `mem_or_mem)
            [`h]))]
         []
         ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `wa
              [(Term.anonymousCtor
                "⟨"
                [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                "⟩")])]])
          []
          (Tactic.exact "exact" (Term.app `nin [`h]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `wb
              [(Term.anonymousCtor
                "⟨"
                [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                "⟩")])]])
          []
          (Tactic.exact "exact" (Term.app `nin [`h]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
               [])]
             "⟩")])]
         []
         [":="
          [(Term.app
            `wb
            [(Term.anonymousCtor
              "⟨"
              [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
              "⟩")])]])
        []
        (Tactic.exact "exact" (Term.app `nin [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `nin [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nin [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `wb
          [(Term.anonymousCtor
            "⟨"
            [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
            "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `wb
       [(Term.anonymousCtor
         "⟨"
         [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_right [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
               [])]
             "⟩")])]
         []
         [":="
          [(Term.app
            `wa
            [(Term.anonymousCtor
              "⟨"
              [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
              "⟩")])]])
        []
        (Tactic.exact "exact" (Term.app `nin [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `nin [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nin [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `nin)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `wa
          [(Term.anonymousCtor
            "⟨"
            [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
            "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `wa
       [(Term.anonymousCtor
         "⟨"
         [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_left [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_left [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wa
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.proj
            (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
            "."
            `IsPrime)
           "."
           `mem_or_mem)
          [`h]))]
       []
       ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
         "."
         `IsPrime)
        "."
        `mem_or_mem)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
        "."
        `IsPrime)
       "."
       `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
       "."
       `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.top [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
         ","
         (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
         ","
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          `ia)
         ","
         («term_+_» `ja "+" `jb)
         ","
         (Term.anonymousCtor
          "⟨"
          [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
           ","
           (Term.app
            `add_mem
            [(Term.typeAscription
              "("
              (Term.subst
               (Term.app `add_comm [`jb `ja])
               "▸"
               [(Term.app `mul_mem [`sb_mem `ra_mem])])
              ":"
              [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
              ")")
             (Term.app `mul_mem [`sa_mem `rb_mem])])]
          "⟩")
         ","
         (Term.anonymousCtor
          "⟨"
          [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
          "⟩")
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
            "⟩")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
        ","
        (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
        ","
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         `ia)
        ","
        («term_+_» `ja "+" `jb)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
          ","
          (Term.app
           `add_mem
           [(Term.typeAscription
             "("
             (Term.subst (Term.app `add_comm [`jb `ja]) "▸" [(Term.app `mul_mem [`sb_mem `ra_mem])])
             ":"
             [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
             ")")
            (Term.app `mul_mem [`sa_mem `rb_mem])])]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
         "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
           "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
         "⟩")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `sa "*" `sb) "," (Term.app `mul_mem [`sa_mem `sb_mem])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem [`sa_mem `sb_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sb_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sa_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `sa "*" `sb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sb
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `sa
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
        ","
        (Term.app
         `add_mem
         [(Term.typeAscription
           "("
           (Term.subst (Term.app `add_comm [`jb `ja]) "▸" [(Term.app `mul_mem [`sb_mem `ra_mem])])
           ":"
           [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
           ")")
          (Term.app `mul_mem [`sa_mem `rb_mem])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `add_mem
       [(Term.typeAscription
         "("
         (Term.subst (Term.app `add_comm [`jb `ja]) "▸" [(Term.app `mul_mem [`sb_mem `ra_mem])])
         ":"
         [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
         ")")
        (Term.app `mul_mem [`sa_mem `rb_mem])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem [`sa_mem `rb_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rb_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sa_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_mem [`sa_mem `rb_mem])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.subst (Term.app `add_comm [`jb `ja]) "▸" [(Term.app `mul_mem [`sb_mem `ra_mem])])
       ":"
       [(«term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» («term_*_» `sb "*" `ra) "∈" (Term.app `𝒜 [(«term_+_» `ja "+" `jb)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `𝒜 [(«term_+_» `ja "+" `jb)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `ja "+" `jb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `jb
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `ja
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `ja "+" `jb) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `sb "*" `ra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ra
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `sb
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst (Term.app `add_comm [`jb `ja]) "▸" [(Term.app `mul_mem [`sb_mem `ra_mem])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem [`sb_mem `ra_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ra_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sb_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `add_comm [`jb `ja])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ja
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `jb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» `sb "*" `ra) "+" («term_*_» `sa "*" `rb))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `sa "*" `rb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rb
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `sa
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `sb "*" `ra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ra
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `sb
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `ja "+" `jb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `jb
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `ja
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       `ia)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ia
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none, [anonymous]) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 69, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `hb [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hb [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `ha [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [(«term_+_» `a "+" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `a "+" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `a "+" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
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
  add_mem'
  ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ )
      ( a b : ∀ x : unop U , at x . 1 )
      ( ha : isLocallyFraction 𝒜 . pred a )
      ( hb : isLocallyFraction 𝒜 . pred b )
    : isLocallyFraction 𝒜 . pred a + b
  :=
    fun
      x
        =>
        by
          rcases ha x with ⟨ Va , ma , ia , ja , ⟨ ra , ra_mem ⟩ , ⟨ sa , sa_mem ⟩ , wa ⟩
            rcases hb x with ⟨ Vb , mb , ib , jb , ⟨ rb , rb_mem ⟩ , ⟨ sb , sb_mem ⟩ , wb ⟩
            refine'
              ⟨
                Va ⊓ Vb
                  ,
                  ⟨ ma , mb ⟩
                  ,
                  opens.inf_le_left _ _ ≫ ia
                  ,
                  ja + jb
                  ,
                  ⟨
                    sb * ra + sa * rb
                      ,
                      add_mem
                        ( add_comm jb ja ▸ mul_mem sb_mem ra_mem : sb * ra ∈ 𝒜 ja + jb )
                          mul_mem sa_mem rb_mem
                    ⟩
                  ,
                  ⟨ sa * sb , mul_mem sa_mem sb_mem ⟩
                  ,
                  fun y => ⟨ fun h => _ , _ ⟩
                ⟩
            ·
              cases' ( y : ProjectiveSpectrum.top 𝒜 ) . IsPrime . mem_or_mem h with h h
                · obtain ⟨ nin , - ⟩ := wa ⟨ y , opens.inf_le_left Va Vb y . 2 ⟩ exact nin h
                · obtain ⟨ nin , - ⟩ := wb ⟨ y , opens.inf_le_right Va Vb y . 2 ⟩ exact nin h
            ·
              simp
                  only
                  [ add_mul , map_add , Pi.add_apply , RingHom.map_mul , ext_iff_val , add_val ]
                obtain ⟨ nin1 , hy1 ⟩ := wa opens.inf_le_left Va Vb y
                obtain ⟨ nin2 , hy2 ⟩ := wb opens.inf_le_right Va Vb y
                dsimp only at hy1 hy2
                erw [ hy1 , hy2 ]
                simpa only [ val_mk' , add_mk , ← Subtype.val_eq_coe , add_comm , mul_comm sa sb ]
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.add_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.add_mem'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_mem' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`a]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" (Term.app `unop [`U]))]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha]
         [":" (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [(«term-_» "-" `a)])))
      (Command.declValSimple
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
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `ha [`x]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `s_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
                     [])]
                   "⟩")])
                [])])
             []
             (Mathlib.Tactic.Choose.choose
              "choose"
              []
              [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
              ["using" `w])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`V
                ","
                `m
                ","
                `i
                ","
                `j
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
                 "⟩")
                ","
                (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`y]
                  []
                  "=>"
                  (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))]
               "⟩"))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `ext_iff_val)
                ","
                (Tactic.simpLemma [] [] `val_mk')
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Pi.neg_apply)
                ","
                (Tactic.simpLemma [] [] `ext_iff_val)
                ","
                (Tactic.simpLemma [] [] `neg_val)
                ","
                (Tactic.simpLemma [] [] `hy)
                ","
                (Tactic.simpLemma [] [] `val_mk')
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                ","
                (Tactic.simpLemma [] [] `neg_mk)]
               "]"]
              [])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
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
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `ha [`x]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
                    [])]
                  "⟩")])
               [])])
            []
            (Mathlib.Tactic.Choose.choose
             "choose"
             []
             [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
             ["using" `w])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`V
               ","
               `m
               ","
               `i
               ","
               `j
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
                "⟩")
               ","
               (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`y]
                 []
                 "=>"
                 (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))]
              "⟩"))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `ext_iff_val)
               ","
               (Tactic.simpLemma [] [] `val_mk')
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Pi.neg_apply)
               ","
               (Tactic.simpLemma [] [] `ext_iff_val)
               ","
               (Tactic.simpLemma [] [] `neg_val)
               ","
               (Tactic.simpLemma [] [] `hy)
               ","
               (Tactic.simpLemma [] [] `val_mk')
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
               ","
               (Tactic.simpLemma [] [] `neg_mk)]
              "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `ha [`x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
                  [])]
                "⟩")])
             [])])
          []
          (Mathlib.Tactic.Choose.choose
           "choose"
           []
           [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
           ["using" `w])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`V
             ","
             `m
             ","
             `i
             ","
             `j
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
              "⟩")
             ","
             (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))]
            "⟩"))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ext_iff_val)
             ","
             (Tactic.simpLemma [] [] `val_mk')
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Pi.neg_apply)
             ","
             (Tactic.simpLemma [] [] `ext_iff_val)
             ","
             (Tactic.simpLemma [] [] `neg_val)
             ","
             (Tactic.simpLemma [] [] `hy)
             ","
             (Tactic.simpLemma [] [] `val_mk')
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `neg_mk)]
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
        [(Tactic.simpLemma [] [] `Pi.neg_apply)
         ","
         (Tactic.simpLemma [] [] `ext_iff_val)
         ","
         (Tactic.simpLemma [] [] `neg_val)
         ","
         (Tactic.simpLemma [] [] `hy)
         ","
         (Tactic.simpLemma [] [] `val_mk')
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `neg_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_mk
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
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.neg_apply
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
        [(Tactic.simpLemma [] [] `ext_iff_val)
         ","
         (Tactic.simpLemma [] [] `val_mk')
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
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
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`V
         ","
         `m
         ","
         `i
         ","
         `j
         ","
         (Term.anonymousCtor
          "⟨"
          [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
          "⟩")
         ","
         (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`V
        ","
        `m
        ","
        `i
        ","
        `j
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
         "⟩")
        ","
        (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `nin [`y]) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nin [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`s "," `s_mem] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term-_» "-" `r) "," (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Submodule.neg_mem [(Term.hole "_") `r_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.neg_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
       ["using" `w])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `ha [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `w)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [(«term-_» "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
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
  neg_mem'
  ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ )
      ( a : ∀ x : unop U , at x . 1 )
      ( ha : isLocallyFraction 𝒜 . pred a )
    : isLocallyFraction 𝒜 . pred - a
  :=
    fun
      x
        =>
        by
          rcases ha x with ⟨ V , m , i , j , ⟨ r , r_mem ⟩ , ⟨ s , s_mem ⟩ , w ⟩
            choose nin hy using w
            refine'
              ⟨
                V
                  ,
                  m
                  ,
                  i
                  ,
                  j
                  ,
                  ⟨ - r , Submodule.neg_mem _ r_mem ⟩
                  ,
                  ⟨ s , s_mem ⟩
                  ,
                  fun y => ⟨ nin y , _ ⟩
                ⟩
            simp only [ ext_iff_val , val_mk' , ← Subtype.val_eq_coe ] at hy
            simp
              only
              [
                Pi.neg_apply , ext_iff_val , neg_val , hy , val_mk' , ← Subtype.val_eq_coe , neg_mk
                ]
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.neg_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.neg_mem'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_mem' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`a `b]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" (Term.app `unop [`U]))]
           ","
           (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            (Term.proj `x "." (fieldIdx "1"))))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha]
         [":" (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hb]
         [":" (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`b])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
         [(«term_*_» `a "*" `b)])))
      (Command.declValSimple
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
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `ha [`x]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hb [`x]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
                ","
                (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
                ","
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 `ia)
                ","
                («term_+_» `ja "+" `jb)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
                 "⟩")
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`y]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                    ","
                    (Term.hole "_")]
                   "⟩")))]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.cases'
                "cases'"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   (Term.proj
                    (Term.proj
                     (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                     "."
                     `IsPrime)
                    "."
                    `mem_or_mem)
                   [`h]))]
                []
                ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Mathlib.Tactic.Choose.choose
                  "choose"
                  []
                  [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
                  ["using"
                   (Term.app
                    `wa
                    [(Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                      "⟩")])])
                 []
                 (Tactic.exact "exact" (Term.app `nin [`h]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Mathlib.Tactic.Choose.choose
                  "choose"
                  []
                  [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
                  ["using"
                   (Term.app
                    `wb
                    [(Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                      "⟩")])])
                 []
                 (Tactic.exact "exact" (Term.app `nin [`h]))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Pi.mul_apply)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.map_mul)]
                 "]"]
                [])
               []
               (Mathlib.Tactic.Choose.choose
                "choose"
                []
                [(Lean.binderIdent `nin1) (Lean.binderIdent `hy1)]
                ["using" (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])])
               []
               (Mathlib.Tactic.Choose.choose
                "choose"
                []
                [(Lean.binderIdent `nin2) (Lean.binderIdent `hy2)]
                ["using" (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val)] "]")
                [(Tactic.location
                  "at"
                  (Tactic.locationHyp [`hy1 `hy2] [(patternIgnore (token.«⊢» "⊢"))]))])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `mul_val)
                  ","
                  (Tactic.rwRule [] `hy1)
                  ","
                  (Tactic.rwRule [] `hy2)]
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
                   [(Tactic.simpLemma [] [] `val_mk')
                    ","
                    (Tactic.simpLemma [] [] `mk_mul)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                   "]")]
                 []))])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
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
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `ha [`x]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hb [`x]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
               ","
               (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
               ","
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                `ia)
               ","
               («term_+_» `ja "+" `jb)
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
                "⟩")
               ","
               (Term.anonymousCtor
                "⟨"
                [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
                "⟩")
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`y]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                   ","
                   (Term.hole "_")]
                  "⟩")))]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.cases'
               "cases'"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                    "."
                    `IsPrime)
                   "."
                   `mem_or_mem)
                  [`h]))]
               []
               ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Mathlib.Tactic.Choose.choose
                 "choose"
                 []
                 [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
                 ["using"
                  (Term.app
                   `wa
                   [(Term.anonymousCtor
                     "⟨"
                     [`y
                      ","
                      (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                     "⟩")])])
                []
                (Tactic.exact "exact" (Term.app `nin [`h]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Mathlib.Tactic.Choose.choose
                 "choose"
                 []
                 [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
                 ["using"
                  (Term.app
                   `wb
                   [(Term.anonymousCtor
                     "⟨"
                     [`y
                      ","
                      (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                     "⟩")])])
                []
                (Tactic.exact "exact" (Term.app `nin [`h]))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Pi.mul_apply)
                 ","
                 (Tactic.simpLemma [] [] `RingHom.map_mul)]
                "]"]
               [])
              []
              (Mathlib.Tactic.Choose.choose
               "choose"
               []
               [(Lean.binderIdent `nin1) (Lean.binderIdent `hy1)]
               ["using" (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])])
              []
              (Mathlib.Tactic.Choose.choose
               "choose"
               []
               [(Lean.binderIdent `nin2) (Lean.binderIdent `hy2)]
               ["using" (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val)] "]")
               [(Tactic.location
                 "at"
                 (Tactic.locationHyp [`hy1 `hy2] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `mul_val)
                 ","
                 (Tactic.rwRule [] `hy1)
                 ","
                 (Tactic.rwRule [] `hy2)]
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
                  [(Tactic.simpLemma [] [] `val_mk')
                   ","
                   (Tactic.simpLemma [] [] `mk_mul)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                  "]")]
                []))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `ha [`x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `hb [`x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
             ","
             (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
             ","
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              `ia)
             ","
             («term_+_» `ja "+" `jb)
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
              "⟩")
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
                "⟩")))]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.cases'
             "cases'"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
                  "."
                  `IsPrime)
                 "."
                 `mem_or_mem)
                [`h]))]
             []
             ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.Choose.choose
               "choose"
               []
               [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
               ["using"
                (Term.app
                 `wa
                 [(Term.anonymousCtor
                   "⟨"
                   [`y
                    ","
                    (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
                   "⟩")])])
              []
              (Tactic.exact "exact" (Term.app `nin [`h]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.Choose.choose
               "choose"
               []
               [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
               ["using"
                (Term.app
                 `wb
                 [(Term.anonymousCtor
                   "⟨"
                   [`y
                    ","
                    (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
                   "⟩")])])
              []
              (Tactic.exact "exact" (Term.app `nin [`h]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Pi.mul_apply) "," (Tactic.simpLemma [] [] `RingHom.map_mul)]
              "]"]
             [])
            []
            (Mathlib.Tactic.Choose.choose
             "choose"
             []
             [(Lean.binderIdent `nin1) (Lean.binderIdent `hy1)]
             ["using" (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])])
            []
            (Mathlib.Tactic.Choose.choose
             "choose"
             []
             [(Lean.binderIdent `nin2) (Lean.binderIdent `hy2)]
             ["using" (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val)] "]")
             [(Tactic.location
               "at"
               (Tactic.locationHyp [`hy1 `hy2] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_val) "," (Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)]
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
                [(Tactic.simpLemma [] [] `val_mk')
                 ","
                 (Tactic.simpLemma [] [] `mk_mul)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                "]")]
              []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Pi.mul_apply) "," (Tactic.simpLemma [] [] `RingHom.map_mul)]
          "]"]
         [])
        []
        (Mathlib.Tactic.Choose.choose
         "choose"
         []
         [(Lean.binderIdent `nin1) (Lean.binderIdent `hy1)]
         ["using" (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])])
        []
        (Mathlib.Tactic.Choose.choose
         "choose"
         []
         [(Lean.binderIdent `nin2) (Lean.binderIdent `hy2)]
         ["using" (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val)] "]")
         [(Tactic.location
           "at"
           (Tactic.locationHyp [`hy1 `hy2] [(patternIgnore (token.«⊢» "⊢"))]))])
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mul_val) "," (Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)]
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
            [(Tactic.simpLemma [] [] `val_mk')
             ","
             (Tactic.simpLemma [] [] `mk_mul)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
            "]")]
          []))])
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
          [(Tactic.simpLemma [] [] `val_mk')
           ","
           (Tactic.simpLemma [] [] `mk_mul)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
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
      `val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_val) "," (Tactic.rwRule [] `hy1) "," (Tactic.rwRule [] `hy2)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ext_iff_val)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hy1 `hy2] [(patternIgnore (token.«⊢» "⊢"))]))])
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
      `ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `nin2) (Lean.binderIdent `hy2)]
       ["using" (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wb [(Term.app `opens.inf_le_right [`Va `Vb `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `nin1) (Lean.binderIdent `hy1)]
       ["using" (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wa [(Term.app `opens.inf_le_left [`Va `Vb `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_left [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_left [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wa
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
        [(Tactic.simpLemma [] [] `Pi.mul_apply) "," (Tactic.simpLemma [] [] `RingHom.map_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.mul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.proj
              (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
              "."
              `IsPrime)
             "."
             `mem_or_mem)
            [`h]))]
         []
         ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.Choose.choose
           "choose"
           []
           [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
           ["using"
            (Term.app
             `wa
             [(Term.anonymousCtor
               "⟨"
               [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
               "⟩")])])
          []
          (Tactic.exact "exact" (Term.app `nin [`h]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.Choose.choose
           "choose"
           []
           [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
           ["using"
            (Term.app
             `wb
             [(Term.anonymousCtor
               "⟨"
               [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
               "⟩")])])
          []
          (Tactic.exact "exact" (Term.app `nin [`h]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Choose.choose
         "choose"
         []
         [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
         ["using"
          (Term.app
           `wb
           [(Term.anonymousCtor
             "⟨"
             [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
             "⟩")])])
        []
        (Tactic.exact "exact" (Term.app `nin [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `nin [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nin [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
       ["using"
        (Term.app
         `wb
         [(Term.anonymousCtor
           "⟨"
           [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
           "⟩")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `wb
       [(Term.anonymousCtor
         "⟨"
         [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y "," (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens.inf_le_right [`Va `Vb `y]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_right [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Choose.choose
         "choose"
         []
         [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
         ["using"
          (Term.app
           `wa
           [(Term.anonymousCtor
             "⟨"
             [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
             "⟩")])])
        []
        (Tactic.exact "exact" (Term.app `nin [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `nin [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nin [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `nin) (Lean.binderIdent `hy)]
       ["using"
        (Term.app
         `wa
         [(Term.anonymousCtor
           "⟨"
           [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
           "⟩")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `wa
       [(Term.anonymousCtor
         "⟨"
         [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y "," (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens.inf_le_left [`Va `Vb `y]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_left [`Va `Vb `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_left [`Va `Vb `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wa
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.proj
            (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
            "."
            `IsPrime)
           "."
           `mem_or_mem)
          [`h]))]
       []
       ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
         "."
         `IsPrime)
        "."
        `mem_or_mem)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
        "."
        `IsPrime)
       "."
       `mem_or_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
       "."
       `IsPrime)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `y ":" [(Term.app `ProjectiveSpectrum.top [`𝒜])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.top [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
         ","
         (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
         ","
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          `ia)
         ","
         («term_+_» `ja "+" `jb)
         ","
         (Term.anonymousCtor
          "⟨"
          [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
          "⟩")
         ","
         (Term.anonymousCtor
          "⟨"
          [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
          "⟩")
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
            "⟩")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
        ","
        (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
        ","
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         `ia)
        ","
        («term_+_» `ja "+" `jb)
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
         "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
           "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
         "⟩")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `sa "*" `sb) "," (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SetLike.mul_mem_graded [`sa_mem `sb_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sb_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sa_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SetLike.mul_mem_graded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `sa "*" `sb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sb
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `sa
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `ra "*" `rb) "," (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SetLike.mul_mem_graded [`ra_mem `rb_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rb_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ra_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SetLike.mul_mem_graded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `ra "*" `rb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rb
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ra
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `ja "+" `jb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `jb
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `ja
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       `ia)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ia
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ma "," `mb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_» `Va " ⊓ " `Vb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Vb
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      `Va
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none, [anonymous]) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 69, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `hb [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Vb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ib)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `jb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rb_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sb_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wb)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hb [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `ha [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Va)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ma)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ia)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ja)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ra_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `sa_mem)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wa)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [(«term_*_» `a "*" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `a "*" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
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
  mul_mem'
  ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ )
      ( a b : ∀ x : unop U , at x . 1 )
      ( ha : isLocallyFraction 𝒜 . pred a )
      ( hb : isLocallyFraction 𝒜 . pred b )
    : isLocallyFraction 𝒜 . pred a * b
  :=
    fun
      x
        =>
        by
          rcases ha x with ⟨ Va , ma , ia , ja , ⟨ ra , ra_mem ⟩ , ⟨ sa , sa_mem ⟩ , wa ⟩
            rcases hb x with ⟨ Vb , mb , ib , jb , ⟨ rb , rb_mem ⟩ , ⟨ sb , sb_mem ⟩ , wb ⟩
            refine'
              ⟨
                Va ⊓ Vb
                  ,
                  ⟨ ma , mb ⟩
                  ,
                  opens.inf_le_left _ _ ≫ ia
                  ,
                  ja + jb
                  ,
                  ⟨ ra * rb , SetLike.mul_mem_graded ra_mem rb_mem ⟩
                  ,
                  ⟨ sa * sb , SetLike.mul_mem_graded sa_mem sb_mem ⟩
                  ,
                  fun y => ⟨ fun h => _ , _ ⟩
                ⟩
            ·
              cases' ( y : ProjectiveSpectrum.top 𝒜 ) . IsPrime . mem_or_mem h with h h
                · choose nin hy using wa ⟨ y , opens.inf_le_left Va Vb y . 2 ⟩ exact nin h
                · choose nin hy using wb ⟨ y , opens.inf_le_right Va Vb y . 2 ⟩ exact nin h
            ·
              simp only [ Pi.mul_apply , RingHom.map_mul ]
                choose nin1 hy1 using wa opens.inf_le_left Va Vb y
                choose nin2 hy2 using wb opens.inf_le_right Va Vb y
                rw [ ext_iff_val ] at hy1 hy2 ⊢
                erw [ mul_val , hy1 , hy2 ]
                simpa only [ val_mk' , mk_mul , ← Subtype.val_eq_coe ]
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.mul_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.mul_mem'

end SectionSubring

section

open SectionSubring

variable {𝒜}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The functions satisfying `is_locally_fraction` form a subring of all dependent functions\n`Π x : U, homogeneous_localization 𝒜 x`.-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `sectionsSubring [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])
           "ᵒᵖ")]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Subring
          [(Term.forall
            "∀"
            [`x]
            [(Term.typeSpec ":" (Term.app `unop [`U]))]
            ","
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
             "at "
             (Term.proj `x "." (fieldIdx "1"))))]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `carrier
           []
           []
           ":="
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `f) [])
            "|"
            (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`f])
            "}"))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `zero_mem' [] [] ":=" (Term.app `zero_mem' [`U]))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `one_mem' [] [] ":=" (Term.app `one_mem' [`U]))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `add_mem' [] [] ":=" (Term.app `add_mem' [`U]))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `neg_mem' [] [] ":=" (Term.app `neg_mem' [`U]))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `mul_mem' [] [] ":=" (Term.app `mul_mem' [`U]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_mem' [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_mem'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `neg_mem' [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `neg_mem'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_mem' [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_mem'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_mem' [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_mem'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_mem' [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_mem'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `f) [])
       "|"
       (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`f])
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `isLocallyFraction [`𝒜]) "." `pred)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isLocallyFraction [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isLocallyFraction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `isLocallyFraction [`𝒜]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Subring
       [(Term.forall
         "∀"
         [`x]
         [(Term.typeSpec ":" (Term.app `unop [`U]))]
         ","
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
          "at "
          (Term.proj `x "." (fieldIdx "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" (Term.app `unop [`U]))]
       ","
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
        "at "
        (Term.proj `x "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
       "at "
       (Term.proj `x "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The functions satisfying `is_locally_fraction` form a subring of all dependent functions
    `Π x : U, homogeneous_localization 𝒜 x`.-/
  def
    sectionsSubring
    ( U : Opens ProjectiveSpectrum.top 𝒜 ᵒᵖ ) : Subring ∀ x : unop U , at x . 1
    where
      carrier := { f | isLocallyFraction 𝒜 . pred f }
        zero_mem' := zero_mem' U
        one_mem' := one_mem' U
        add_mem' := add_mem' U
        neg_mem' := neg_mem' U
        mul_mem' := mul_mem' U
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring

end

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.-/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.structure_sheaf_in_Type AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structureSheafInType

instance commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    CommRing ((structureSheafInType 𝒜).1.obj U) :=
  (sectionsSubring U).toCommRing
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.comm_ring_structure_sheaf_in_Type_obj AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.commRingStructureSheafInTypeObj

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.-/
@[simps]
def structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜)
    where
  obj U := CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map U V i :=
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl
      map_one' := rfl
      map_mul' := fun x y => rfl }
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_in_CommRing AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRing

/-- Some glue, verifying that that structure presheaf valued in `CommRing` agrees with the `Type`
valued structure presheaf.-/
def structurePresheafCompForget :
    structurePresheafInCommRing 𝒜 ⋙ forget CommRingCat ≅ (structureSheafInType 𝒜).1 :=
  NatIso.ofComponents (fun U => Iso.refl _) (by tidy)
#align
  algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_comp_forget AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafCompForget

end ProjectiveSpectrum.StructureSheaf

namespace ProjectiveSpectrum

open TopCat.Presheaf ProjectiveSpectrum.StructureSheaf Opens

/-- The structure sheaf on `Proj` 𝒜, valued in `CommRing`.-/
def ProjCat.structureSheaf : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          is_sheaf_iff_is_sheaf_comp
          _ _).mpr
      (is_sheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).cond)⟩
#align
  algebraic_geometry.projective_spectrum.Proj.structure_sheaf AlgebraicGeometry.ProjectiveSpectrum.ProjCat.structureSheaf

end ProjectiveSpectrum

section

open ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

@[simp]
theorem res_apply (U V : Opens (ProjectiveSpectrum.top 𝒜)) (i : V ⟶ U)
    (s : (ProjCat.structureSheaf 𝒜).1.obj (op U)) (x : V) :
    ((ProjCat.structureSheaf 𝒜).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl
#align algebraic_geometry.res_apply AlgebraicGeometry.res_apply

/-- `Proj` of a graded ring as a `SheafedSpace`-/
def ProjCat.toSheafedSpace : SheafedSpaceCat CommRingCat
    where
  carrier := TopCat.of (ProjectiveSpectrum 𝒜)
  Presheaf := (ProjCat.structureSheaf 𝒜).1
  IsSheaf := (ProjCat.structureSheaf 𝒜).2
#align algebraic_geometry.Proj.to_SheafedSpace AlgebraicGeometry.ProjCat.toSheafedSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The ring homomorphism that takes a section of the structure sheaf of `Proj` on the open set `U`,\nimplemented as a subtype of dependent functions to localizations at homogeneous prime ideals, and\nevaluates the section on the point corresponding to a given homogeneous prime ideal. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `openToLocalization [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.app `ProjectiveSpectrum.top [`𝒜])])]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_∈_» `x "∈" `U)] [] ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app
           (Term.proj
            (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1"))
            "."
            `obj)
           [(Term.app `op [`U])])
          " ⟶ "
          (Term.app
           `CommRingCat.of
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
             "at "
             `x)])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`s]
           []
           ":="
           (Term.typeAscription
            "("
            (Term.app (Term.proj `s "." (fieldIdx "1")) [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
            ":"
            [(Term.hole "_")]
            ")"))))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `map_one' [] [] ":=" `rfl)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `map_mul' [(Term.hole "_") (Term.hole "_")] [] ":=" `rfl)))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `map_zero' [] [] ":=" `rfl)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `map_add' [(Term.hole "_") (Term.hole "_")] [] ":=" `rfl)))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (Term.proj `s "." (fieldIdx "1")) [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s "." (fieldIdx "1")) [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_»
       (Term.app
        (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")) "." `obj)
        [(Term.app `op [`U])])
       " ⟶ "
       (Term.app
        `CommRingCat.of
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `CommRingCat.of
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The ring homomorphism that takes a section of the structure sheaf of `Proj` on the open set `U`,
    implemented as a subtype of dependent functions to localizations at homogeneous prime ideals, and
    evaluates the section on the point corresponding to a given homogeneous prime ideal. -/
  def
    openToLocalization
    ( U : Opens ProjectiveSpectrum.top 𝒜 ) ( x : ProjectiveSpectrum.top 𝒜 ) ( hx : x ∈ U )
      : ProjCat.structureSheaf 𝒜 . 1 . obj op U ⟶ CommRingCat.of at x
    where
      toFun s := ( s . 1 ⟨ x , hx ⟩ : _ )
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl
#align algebraic_geometry.open_to_localization AlgebraicGeometry.openToLocalization

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding\nto a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,\nformed by gluing the `open_to_localization` maps. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `stalkToFiberRingHom [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app
           (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
           [`x])
          " ⟶ "
          (Term.app
           `CommRingCat.of
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
             "at "
             `x)])))])
      (Command.declValSimple
       ":="
       (Term.app
        `Limits.colimit.desc
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          (Term.proj (Term.app `OpenNhds.inclusion [`x]) "." `op)
          " ⋙ "
          (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")))
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `x []) ":=" (Term.hole "_"))
           []
           (Term.structInstField
            (Term.structInstLVal `ι [])
            ":="
            (Term.structInst
             "{"
             []
             [(Term.structInstField
               (Term.structInstLVal `app [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`U]
                 []
                 "=>"
                 (Term.app
                  `openToLocalization
                  [`𝒜
                   (Term.app
                    (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
                    [(Term.app `unop [`U])])
                   `x
                   (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))]))))]
             (Term.optEllipsis [])
             []
             "}"))]
          (Term.optEllipsis [])
          []
          "}")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Limits.colimit.desc
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (Term.proj (Term.app `OpenNhds.inclusion [`x]) "." `op)
         " ⋙ "
         (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")))
        (Term.structInst
         "{"
         []
         [(Term.structInstField (Term.structInstLVal `x []) ":=" (Term.hole "_"))
          []
          (Term.structInstField
           (Term.structInstLVal `ι [])
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `app [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`U]
                []
                "=>"
                (Term.app
                 `openToLocalization
                 [`𝒜
                  (Term.app
                   (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
                   [(Term.app `unop [`U])])
                  `x
                  (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))]))))]
            (Term.optEllipsis [])
            []
            "}"))]
         (Term.optEllipsis [])
         []
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `x []) ":=" (Term.hole "_"))
        []
        (Term.structInstField
         (Term.structInstLVal `ι [])
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField
            (Term.structInstLVal `app [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`U]
              []
              "=>"
              (Term.app
               `openToLocalization
               [`𝒜
                (Term.app
                 (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
                 [(Term.app `unop [`U])])
                `x
                (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))]))))]
          (Term.optEllipsis [])
          []
          "}"))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `app [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`U]
           []
           "=>"
           (Term.app
            `openToLocalization
            [`𝒜
             (Term.app
              (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
              [(Term.app `unop [`U])])
             `x
             (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`U]
        []
        "=>"
        (Term.app
         `openToLocalization
         [`𝒜
          (Term.app
           (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
           [(Term.app `unop [`U])])
          `x
          (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `openToLocalization
       [`𝒜
        (Term.app
         (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
         [(Term.app `unop [`U])])
        `x
        (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `unop [`U]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [`U]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
       [(Term.app `unop [`U])])
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
      (Term.proj (Term.app `OpenNhds.inclusion [(Term.hole "_")]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `OpenNhds.inclusion [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `OpenNhds.inclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `OpenNhds.inclusion [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `OpenNhds.inclusion [(Term.hole "_")]) ")") "." `obj)
      [(Term.paren "(" (Term.app `unop [`U]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `openToLocalization
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.proj (Term.app `OpenNhds.inclusion [`x]) "." `op)
       " ⋙ "
       (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjCat.structureSheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjCat.structureSheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjCat.structureSheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.proj (Term.app `OpenNhds.inclusion [`x]) "." `op)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `OpenNhds.inclusion [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `OpenNhds.inclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `OpenNhds.inclusion [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      (Term.proj (Term.paren "(" (Term.app `OpenNhds.inclusion [`x]) ")") "." `op)
      " ⋙ "
      (Term.proj (Term.paren "(" (Term.app `ProjCat.structureSheaf [`𝒜]) ")") "." (fieldIdx "1")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Limits.colimit.desc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_»
       (Term.app
        (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
        [`x])
       " ⟶ "
       (Term.app
        `CommRingCat.of
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `CommRingCat.of
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
    to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
    formed by gluing the `open_to_localization` maps. -/
  def
    stalkToFiberRingHom
    ( x : ProjectiveSpectrum.top 𝒜 )
      : ProjCat.structureSheaf 𝒜 . Presheaf . stalk x ⟶ CommRingCat.of at x
    :=
      Limits.colimit.desc
        OpenNhds.inclusion x . op ⋙ ProjCat.structureSheaf 𝒜 . 1
          {
            x := _
              ι
                :=
                {
                  app
                    :=
                    fun U => openToLocalization 𝒜 OpenNhds.inclusion _ . obj unop U x unop U . 2
                  }
            }
#align algebraic_geometry.stalk_to_fiber_ring_hom AlgebraicGeometry.stalkToFiberRingHom

@[simp]
theorem germ_comp_stalk_to_fiber_ring_hom (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U) :
    (ProjCat.structureSheaf 𝒜).Presheaf.germ x ≫ stalkToFiberRingHom 𝒜 x =
      openToLocalization 𝒜 U x x.2 :=
  Limits.colimit.ι_desc _ _
#align
  algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom AlgebraicGeometry.germ_comp_stalk_to_fiber_ring_hom

@[simp]
theorem stalk_to_fiber_ring_hom_germ' (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (ProjCat.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((ProjCat.structureSheaf 𝒜).Presheaf.germ ⟨x, hx⟩ s) =
      (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom 𝒜 U ⟨x, hx⟩ : _) s
#align
  algebraic_geometry.stalk_to_fiber_ring_hom_germ' AlgebraicGeometry.stalk_to_fiber_ring_hom_germ'

@[simp]
theorem stalk_to_fiber_ring_hom_germ (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U)
    (s : (ProjCat.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((ProjCat.structureSheaf 𝒜).Presheaf.germ x s) = s.1 x :=
  by
  cases x
  exact stalk_to_fiber_ring_hom_germ' 𝒜 U _ _ _
#align
  algebraic_geometry.stalk_to_fiber_ring_hom_germ AlgebraicGeometry.stalk_to_fiber_ring_hom_germ

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HomogeneousLocalization.mem_basic_open [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» `x "∈" (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_basic_open)] "]")
            [])
           []
           (Tactic.exact "exact" `f.denom_mem)])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_basic_open)] "]")
           [])
          []
          (Tactic.exact "exact" `f.denom_mem)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `f.denom_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.denom_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ProjectiveSpectrum.mem_basic_open)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_» `x "∈" (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
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
  HomogeneousLocalization.mem_basic_open
  ( x : ProjectiveSpectrum.top 𝒜 ) ( f : at x ) : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f . denom
  := by rw [ ProjectiveSpectrum.mem_basic_open ] exact f.denom_mem
#align
  algebraic_geometry.homogeneous_localization.mem_basic_open AlgebraicGeometry.HomogeneousLocalization.mem_basic_open

variable (𝒜)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function\nsuch that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the\nbasic open set `D(f.denom)`-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `sectionInBasicOpen [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`f]
          [(Term.typeSpec
            ":"
            (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
             "at "
             `x))]
          ","
          (Term.app
           (Term.proj
            (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1"))
            "."
            `obj)
           [(Term.app
             `op
             [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])])])))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`f]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`y]
             []
             "=>"
             (Term.app
              `Quotient.mk'
              [(Term.anonymousCtor
                "⟨"
                [(Term.proj `f "." `deg)
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                  "⟩")
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                  "⟩")
                 ","
                 (Term.proj `y "." (fieldIdx "2"))]
                "⟩")])))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`y]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
               ","
               (Term.proj `y "." (fieldIdx "2"))
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.app
                  (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                  [(Term.hole "_")])
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.proj `f "." `deg)
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                      "⟩")
                     ","
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                      "⟩")
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`z]
                       []
                       "=>"
                       (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
                    "⟩")]
                  "⟩")]
                "⟩")]
              "⟩")))]
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
        [`f]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`y]
            []
            "=>"
            (Term.app
             `Quotient.mk'
             [(Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `deg)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                 "⟩")
                ","
                (Term.proj `y "." (fieldIdx "2"))]
               "⟩")])))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [`y]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
              ","
              (Term.proj `y "." (fieldIdx "2"))
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.app
                 (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                 [(Term.hole "_")])
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.proj `f "." `deg)
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                     "⟩")
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                     "⟩")
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`z]
                      []
                      "=>"
                      (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
                   "⟩")]
                 "⟩")]
               "⟩")]
             "⟩")))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.app
           `Quotient.mk'
           [(Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `deg)
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
               "⟩")
              ","
              (Term.proj `y "." (fieldIdx "2"))]
             "⟩")])))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
            ","
            (Term.proj `y "." (fieldIdx "2"))
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.app
               (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
               [(Term.hole "_")])
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `deg)
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                   "⟩")
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                   "⟩")
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`z]
                    []
                    "=>"
                    (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
                 "⟩")]
               "⟩")]
             "⟩")]
           "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
          ","
          (Term.proj `y "." (fieldIdx "2"))
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `deg)
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
                 "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
                 "⟩")
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`z]
                  []
                  "=>"
                  (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
               "⟩")]
             "⟩")]
           "⟩")]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
        ","
        (Term.proj `y "." (fieldIdx "2"))
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.proj `f "." `deg)
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
               "⟩")
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [`z]
                []
                "=>"
                (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
             "⟩")]
           "⟩")]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `f "." `deg)
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
             "⟩")
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [`z]
              []
              "=>"
              (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
           "⟩")]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj `f "." `deg)
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
           "⟩")
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [`z]
            []
            "=>"
            (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
         "⟩")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`z]
          []
          "=>"
          (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `z "." (fieldIdx "2")) "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `z "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom_mem_deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `num_mem_deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `num)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.app
         `Quotient.mk'
         [(Term.anonymousCtor
           "⟨"
           [(Term.proj `f "." `deg)
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
             "⟩")
            ","
            (Term.proj `y "." (fieldIdx "2"))]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.mk'
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj `f "." `deg)
          ","
          (Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
           "⟩")
          ","
          (Term.proj `y "." (fieldIdx "2"))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj `f "." `deg)
        ","
        (Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)]
         "⟩")
        ","
        (Term.proj `y "." (fieldIdx "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `f "." `denom) "," (Term.proj `f "." `denom_mem_deg)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom_mem_deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `f "." `num) "," (Term.proj `f "." `num_mem_deg)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `num_mem_deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `num)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `deg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.mk'
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`f]
       [(Term.typeSpec
         ":"
         (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x))]
       ","
       (Term.app
        (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")) "." `obj)
        [(Term.app `op [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")) "." `obj)
       [(Term.app `op [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `op [(Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `op
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `op
      [(Term.paren
        "("
        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 (Term.proj `f "." `denom)])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1")) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjCat.structureSheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjCat.structureSheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjCat.structureSheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function
    such that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the
    basic open set `D(f.denom)`-/
  def
    sectionInBasicOpen
    ( x : ProjectiveSpectrum.top 𝒜 )
      : ∀ f : at x , ProjCat.structureSheaf 𝒜 . 1 . obj op ProjectiveSpectrum.basicOpen 𝒜 f . denom
    :=
      fun
        f
          =>
          ⟨
            fun
                y
                  =>
                  Quotient.mk'
                    ⟨
                      f . deg
                        ,
                        ⟨ f . num , f . num_mem_deg ⟩
                        ,
                        ⟨ f . denom , f . denom_mem_deg ⟩
                        ,
                        y . 2
                      ⟩
              ,
              fun
                y
                  =>
                  ⟨
                    ProjectiveSpectrum.basicOpen 𝒜 f . denom
                      ,
                      y . 2
                      ,
                      ⟨
                        𝟙 _
                          ,
                          ⟨
                            f . deg
                              ,
                              ⟨
                                ⟨ f . num , f . num_mem_deg ⟩
                                  ,
                                  ⟨ f . denom , f . denom_mem_deg ⟩
                                  ,
                                  fun z => ⟨ z . 2 , rfl ⟩
                                ⟩
                            ⟩
                        ⟩
                    ⟩
            ⟩
#align algebraic_geometry.section_in_basic_open AlgebraicGeometry.sectionInBasicOpen

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the\nstalk at `x` obtained by `section_in_basic_open`. This is the inverse of `stalk_to_fiber_ring_hom`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `homogeneousLocalizationToStalk [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
          "→"
          (Term.app
           (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
           [`x])))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`f]
         []
         "=>"
         (Term.app
          (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `germ)
          [(Term.typeAscription
            "("
            (Term.anonymousCtor
             "⟨"
             [`x "," (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])]
             "⟩")
            ":"
            [(Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") (Term.proj `f "." `denom)])]
            ")")
           (Term.app `sectionInBasicOpen [(Term.hole "_") `x `f])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.app
         (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `germ)
         [(Term.typeAscription
           "("
           (Term.anonymousCtor
            "⟨"
            [`x "," (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])]
            "⟩")
           ":"
           [(Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") (Term.proj `f "." `denom)])]
           ")")
          (Term.app `sectionInBasicOpen [(Term.hole "_") `x `f])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `germ)
       [(Term.typeAscription
         "("
         (Term.anonymousCtor
          "⟨"
          [`x "," (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])]
          "⟩")
         ":"
         [(Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") (Term.proj `f "." `denom)])]
         ")")
        (Term.app `sectionInBasicOpen [(Term.hole "_") `x `f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sectionInBasicOpen [(Term.hole "_") `x `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sectionInBasicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sectionInBasicOpen [(Term.hole "_") `x `f])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.anonymousCtor
        "⟨"
        [`x "," (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])]
        "⟩")
       ":"
       [(Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") (Term.proj `f "." `denom)])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") (Term.proj `f "." `denom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `denom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x "," (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HomogeneousLocalization.mem_basic_open [(Term.hole "_") `x `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HomogeneousLocalization.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `germ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjCat.structureSheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjCat.structureSheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjCat.structureSheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
       "→"
       (Term.app
        (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
        [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
       [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjCat.structureSheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjCat.structureSheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjCat.structureSheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the
    stalk at `x` obtained by `section_in_basic_open`. This is the inverse of `stalk_to_fiber_ring_hom`.
    -/
  def
    homogeneousLocalizationToStalk
    ( x : ProjectiveSpectrum.top 𝒜 ) : at x → ProjCat.structureSheaf 𝒜 . Presheaf . stalk x
    :=
      fun
        f
          =>
          ProjCat.structureSheaf 𝒜 . Presheaf . germ
            (
                ⟨ x , HomogeneousLocalization.mem_basic_open _ x f ⟩
                :
                ProjectiveSpectrum.basicOpen _ f . denom
                )
              sectionInBasicOpen _ x f
#align
  algebraic_geometry.homogeneous_localization_to_stalk AlgebraicGeometry.homogeneousLocalizationToStalk

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Using `homogeneous_localization_to_stalk`, we construct a ring isomorphism between stalk at `x`\nand homogeneous localization at `x` for any point `x` in `Proj`.-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ProjCat.stalkIso' [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Ring.Equiv.«term_≃+*_»
          (Term.app
           (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
           [`x])
          " ≃+* "
          (Term.app
           `CommRingCat.of
           [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
             "at "
             `x)])))])
      (Command.declValSimple
       ":="
       (Term.app
        `RingEquiv.ofBijective
        [(Term.app `stalkToFiberRingHom [(Term.hole "_") `x])
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`z1 `z2 `eq1]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     (Term.proj
                      (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                      "."
                      `germ_exist)
                     [`x `z1])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     (Term.proj
                      (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                      "."
                      `germ_exist)
                     [`x `z2])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `j1)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
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
                                   [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
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
                                   [(Std.Tactic.RCases.rcasesPat.one `b1)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                                  [])]
                                "⟩")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                             [])]
                           "⟩")])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     (Term.proj `s1 "." (fieldIdx "2"))
                     [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                                   [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
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
                                   [(Std.Tactic.RCases.rcasesPat.one `b2)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                                  [])]
                                "⟩")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                             [])]
                           "⟩")])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     (Term.proj `s2 "." (fieldIdx "2"))
                     [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
                 []
                 (Tactic.dsimp
                  "dsimp"
                  []
                  []
                  ["only"]
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `stalk_to_fiber_ring_hom_germ
                      [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `stalk_to_fiber_ring_hom_germ
                      [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                 []
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                   "="
                   (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
                  [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Localization.mk_eq_mk')
                    ","
                    (Tactic.rwRule [] `IsLocalization.eq)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hc)])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [`eq3]])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                   "]"]
                  [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`eq3' []]
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [(Term.explicitBinder
                         "("
                         [`y]
                         [":" (Term.app `ProjectiveSpectrum.top [`𝒜])]
                         []
                         ")")
                        (Term.explicitBinder
                         "("
                         [`hy]
                         [":"
                          («term_∈_»
                           `y
                           "∈"
                           (Order.Basic.«term_⊓_»
                            (Order.Basic.«term_⊓_»
                             (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                             " ⊓ "
                             (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                            " ⊓ "
                            (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
                         []
                         ")")]
                       []
                       ","
                       («term_=_»
                        (Term.typeAscription
                         "("
                         (Term.app
                          `Localization.mk
                          [`a1
                           (Term.anonymousCtor
                            "⟨"
                            [`b1
                             ","
                             (Term.show
                              "show"
                              («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                              (Term.byTactic'
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Tactic.«tactic_<;>_»
                                   (Tactic.rwSeq
                                    "rw"
                                    []
                                    (Tactic.rwRuleSeq
                                     "["
                                     [(Tactic.rwRule
                                       [(patternIgnore (token.«← » "←"))]
                                       `ProjectiveSpectrum.mem_basic_open)]
                                     "]")
                                    [])
                                   "<;>"
                                   (Tactic.exact
                                    "exact"
                                    (Term.app
                                     `le_of_hom
                                     [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                       (Term.app
                                        `opens.inf_le_left
                                        [(Term.hole "_") (Term.hole "_")])
                                       " ≫ "
                                       (Term.app
                                        `opens.inf_le_left
                                        [(Term.hole "_") (Term.hole "_")]))
                                      `hy])))]))))]
                            "⟩")])
                         ":"
                         [(Term.app
                           `Localization.AtPrime
                           [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
                         ")")
                        "="
                        (Term.app
                         `Localization.mk
                         [`a2
                          (Term.anonymousCtor
                           "⟨"
                           [`b2
                            ","
                            (Term.show
                             "show"
                             («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Tactic.«tactic_<;>_»
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule
                                      [(patternIgnore (token.«← » "←"))]
                                      `ProjectiveSpectrum.mem_basic_open)]
                                    "]")
                                   [])
                                  "<;>"
                                  (Tactic.exact
                                   "exact"
                                   (Term.app
                                    `le_of_hom
                                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                      (Term.app
                                       `opens.inf_le_left
                                       [(Term.hole "_") (Term.hole "_")])
                                      " ≫ "
                                      (Term.app
                                       `opens.inf_le_right
                                       [(Term.hole "_") (Term.hole "_")]))
                                     `hy])))]))))]
                           "⟩")]))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [`y `hy])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `Localization.mk_eq_mk')
                           ","
                           (Tactic.rwRule [] `IsLocalization.eq)]
                          "]")
                         [])
                        []
                        (Tactic.exact
                         "exact"
                         (Term.anonymousCtor
                          "⟨"
                          [(Term.anonymousCtor
                            "⟨"
                            [`c
                             ","
                             (Term.show
                              "show"
                              («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                              (Term.byTactic'
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Tactic.«tactic_<;>_»
                                   (Tactic.rwSeq
                                    "rw"
                                    []
                                    (Tactic.rwRuleSeq
                                     "["
                                     [(Tactic.rwRule
                                       [(patternIgnore (token.«← » "←"))]
                                       `ProjectiveSpectrum.mem_basic_open)]
                                     "]")
                                    [])
                                   "<;>"
                                   (Tactic.exact
                                    "exact"
                                    (Term.app
                                     `le_of_hom
                                     [(Term.app
                                       `opens.inf_le_right
                                       [(Term.hole "_") (Term.hole "_")])
                                      `hy])))]))))]
                            "⟩")
                           ","
                           `eq3]
                          "⟩"))]))))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `presheaf.germ_ext
                   [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
                    (Order.Basic.«term_⊓_»
                     (Order.Basic.«term_⊓_»
                      (Order.Basic.«term_⊓_»
                       (Order.Basic.«term_⊓_»
                        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
                        " ⊓ "
                        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
                       " ⊓ "
                       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
                      " ⊓ "
                      `v1)
                     " ⊓ "
                     `v2)
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor
                         "⟨"
                         [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
                         "⟩")
                        ","
                        `memv1]
                       "⟩")
                      ","
                      `memv2]
                     "⟩")
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      `i1))
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     `i2)
                    (Term.hole "_")]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]")
                  [])
                 []
                 (Std.Tactic.Ext.tacticExt1___
                  "ext1"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"]
                  [])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     `hs1
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.hole "_")
                        ","
                        (Term.app
                         `le_of_hom
                         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                          (Term.proj `y "." (fieldIdx "2"))])]
                       "⟩")])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     `hs2
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.hole "_")
                        ","
                        (Term.app
                         `le_of_hom
                         [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                          (Term.proj `y "." (fieldIdx "2"))])]
                       "⟩")])]])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `eq6)
                    ","
                    (Tactic.rwRule [] `eq7)
                    ","
                    (Tactic.rwRule [] `Quotient.eq)]
                   "]")
                  [])
                 []
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                   "="
                   (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `eq3'
                   [(Term.hole "_")
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.app
                         `le_of_hom
                         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                             " ≫ "
                             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
                          (Term.proj `y "." (fieldIdx "2"))])
                        ","
                        (Term.app
                         `le_of_hom
                         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                             " ≫ "
                             (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
                          (Term.proj `y "." (fieldIdx "2"))])]
                       "⟩")
                      ","
                      (Term.app
                       `le_of_hom
                       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                         " ≫ "
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
                        (Term.proj `y "." (fieldIdx "2"))])]
                     "⟩")]))])))))
           ","
           (Term.app
            (Term.proj `Function.surjective_iff_hasRightInverse "." `mpr)
            [(Term.anonymousCtor
              "⟨"
              [(Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`f]
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
                       [(Tactic.rwRule [] `homogeneous_localization_to_stalk)]
                       "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app
                          `stalk_to_fiber_ring_hom_germ
                          [`𝒜
                           (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                           (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                           (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
                       "]")
                      [])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `section_in_basic_open)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
                        ","
                        (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
                        ","
                        (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
                        ","
                        (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
                       "]"]
                      [])
                     []
                     (Tactic.tacticRfl "rfl")])))))]
              "⟩")])]
          "⟩")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `RingEquiv.ofBijective
       [(Term.app `stalkToFiberRingHom [(Term.hole "_") `x])
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`z1 `z2 `eq1]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    (Term.proj
                     (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                     "."
                     `germ_exist)
                    [`x `z1])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    (Term.proj
                     (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                     "."
                     `germ_exist)
                    [`x `z2])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j1)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
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
                                  [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
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
                                  [(Std.Tactic.RCases.rcasesPat.one `b1)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                                 [])]
                               "⟩")])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    (Term.proj `s1 "." (fieldIdx "2"))
                    [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                                  [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
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
                                  [(Std.Tactic.RCases.rcasesPat.one `b2)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                                 [])]
                               "⟩")])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    (Term.proj `s2 "." (fieldIdx "2"))
                    [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
                []
                (Tactic.dsimp
                 "dsimp"
                 []
                 []
                 ["only"]
                 []
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app
                     `stalk_to_fiber_ring_hom_germ
                     [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app
                     `stalk_to_fiber_ring_hom_germ
                     [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                  "="
                  (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
                 [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Localization.mk_eq_mk')
                   ","
                   (Tactic.rwRule [] `IsLocalization.eq)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                            [])]
                          "⟩")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`eq3]])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                  "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`eq3' []]
                   [(Term.typeSpec
                     ":"
                     (Term.forall
                      "∀"
                      [(Term.explicitBinder
                        "("
                        [`y]
                        [":" (Term.app `ProjectiveSpectrum.top [`𝒜])]
                        []
                        ")")
                       (Term.explicitBinder
                        "("
                        [`hy]
                        [":"
                         («term_∈_»
                          `y
                          "∈"
                          (Order.Basic.«term_⊓_»
                           (Order.Basic.«term_⊓_»
                            (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                            " ⊓ "
                            (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                           " ⊓ "
                           (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
                        []
                        ")")]
                      []
                      ","
                      («term_=_»
                       (Term.typeAscription
                        "("
                        (Term.app
                         `Localization.mk
                         [`a1
                          (Term.anonymousCtor
                           "⟨"
                           [`b1
                            ","
                            (Term.show
                             "show"
                             («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Tactic.«tactic_<;>_»
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule
                                      [(patternIgnore (token.«← » "←"))]
                                      `ProjectiveSpectrum.mem_basic_open)]
                                    "]")
                                   [])
                                  "<;>"
                                  (Tactic.exact
                                   "exact"
                                   (Term.app
                                    `le_of_hom
                                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                      (Term.app
                                       `opens.inf_le_left
                                       [(Term.hole "_") (Term.hole "_")])
                                      " ≫ "
                                      (Term.app
                                       `opens.inf_le_left
                                       [(Term.hole "_") (Term.hole "_")]))
                                     `hy])))]))))]
                           "⟩")])
                        ":"
                        [(Term.app
                          `Localization.AtPrime
                          [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
                        ")")
                       "="
                       (Term.app
                        `Localization.mk
                        [`a2
                         (Term.anonymousCtor
                          "⟨"
                          [`b2
                           ","
                           (Term.show
                            "show"
                            («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                            (Term.byTactic'
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.«tactic_<;>_»
                                 (Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq
                                   "["
                                   [(Tactic.rwRule
                                     [(patternIgnore (token.«← » "←"))]
                                     `ProjectiveSpectrum.mem_basic_open)]
                                   "]")
                                  [])
                                 "<;>"
                                 (Tactic.exact
                                  "exact"
                                  (Term.app
                                   `le_of_hom
                                   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                     " ≫ "
                                     (Term.app
                                      `opens.inf_le_right
                                      [(Term.hole "_") (Term.hole "_")]))
                                    `hy])))]))))]
                          "⟩")]))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.intro "intro" [`y `hy])
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `Localization.mk_eq_mk')
                          ","
                          (Tactic.rwRule [] `IsLocalization.eq)]
                         "]")
                        [])
                       []
                       (Tactic.exact
                        "exact"
                        (Term.anonymousCtor
                         "⟨"
                         [(Term.anonymousCtor
                           "⟨"
                           [`c
                            ","
                            (Term.show
                             "show"
                             («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Tactic.«tactic_<;>_»
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule
                                      [(patternIgnore (token.«← » "←"))]
                                      `ProjectiveSpectrum.mem_basic_open)]
                                    "]")
                                   [])
                                  "<;>"
                                  (Tactic.exact
                                   "exact"
                                   (Term.app
                                    `le_of_hom
                                    [(Term.app
                                      `opens.inf_le_right
                                      [(Term.hole "_") (Term.hole "_")])
                                     `hy])))]))))]
                           "⟩")
                          ","
                          `eq3]
                         "⟩"))]))))))
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `presheaf.germ_ext
                  [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
                   (Order.Basic.«term_⊓_»
                    (Order.Basic.«term_⊓_»
                     (Order.Basic.«term_⊓_»
                      (Order.Basic.«term_⊓_»
                       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
                       " ⊓ "
                       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
                      " ⊓ "
                      (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
                     " ⊓ "
                     `v1)
                    " ⊓ "
                    `v2)
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor
                        "⟨"
                        [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
                        "⟩")
                       ","
                       `memv1]
                      "⟩")
                     ","
                     `memv2]
                    "⟩")
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     `i1))
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    `i2)
                   (Term.hole "_")]))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]")
                 [])
                []
                (Std.Tactic.Ext.tacticExt1___
                 "ext1"
                 [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"]
                 [])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    `hs1
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.hole "_")
                       ","
                       (Term.app
                        `le_of_hom
                        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                         (Term.proj `y "." (fieldIdx "2"))])]
                      "⟩")])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
                       [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    `hs2
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.hole "_")
                       ","
                       (Term.app
                        `le_of_hom
                        [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                         (Term.proj `y "." (fieldIdx "2"))])]
                      "⟩")])]])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 []
                 [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `eq6)
                   ","
                   (Tactic.rwRule [] `eq7)
                   ","
                   (Tactic.rwRule [] `Quotient.eq)]
                  "]")
                 [])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                  "="
                  (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `eq3'
                  [(Term.hole "_")
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.app
                        `le_of_hom
                        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                            " ≫ "
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
                         (Term.proj `y "." (fieldIdx "2"))])
                       ","
                       (Term.app
                        `le_of_hom
                        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                            " ≫ "
                            (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
                         (Term.proj `y "." (fieldIdx "2"))])]
                      "⟩")
                     ","
                     (Term.app
                      `le_of_hom
                      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                         " ≫ "
                         (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
                       (Term.proj `y "." (fieldIdx "2"))])]
                    "⟩")]))])))))
          ","
          (Term.app
           (Term.proj `Function.surjective_iff_hasRightInverse "." `mpr)
           [(Term.anonymousCtor
             "⟨"
             [(Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [`f]
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
                      [(Tactic.rwRule [] `homogeneous_localization_to_stalk)]
                      "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         `stalk_to_fiber_ring_hom_germ
                         [`𝒜
                          (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                          (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                          (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
                      "]")
                     [])
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `section_in_basic_open)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
                       ","
                       (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
                       ","
                       (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
                       ","
                       (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
                      "]"]
                     [])
                    []
                    (Tactic.tacticRfl "rfl")])))))]
             "⟩")])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`z1 `z2 `eq1]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                   "."
                   `germ_exist)
                  [`x `z1])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                   "."
                   `germ_exist)
                  [`x `z2])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j1)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
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
                                [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
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
                                [(Std.Tactic.RCases.rcasesPat.one `b1)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                               [])]
                             "⟩")])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj `s1 "." (fieldIdx "2"))
                  [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                                [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
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
                                [(Std.Tactic.RCases.rcasesPat.one `b2)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                               [])]
                             "⟩")])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj `s2 "." (fieldIdx "2"))
                  [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
              []
              (Tactic.dsimp
               "dsimp"
               []
               []
               ["only"]
               []
               [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.app
                   `stalk_to_fiber_ring_hom_germ
                   [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `stalk_to_fiber_ring_hom_germ
                   [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
              []
              (Tactic.change
               "change"
               («term_=_»
                (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                "="
                (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
               [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Localization.mk_eq_mk')
                 ","
                 (Tactic.rwRule [] `IsLocalization.eq)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                     [])]
                   "⟩")])]
               []
               [":=" [`eq3]])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`eq3' []]
                 [(Term.typeSpec
                   ":"
                   (Term.forall
                    "∀"
                    [(Term.explicitBinder
                      "("
                      [`y]
                      [":" (Term.app `ProjectiveSpectrum.top [`𝒜])]
                      []
                      ")")
                     (Term.explicitBinder
                      "("
                      [`hy]
                      [":"
                       («term_∈_»
                        `y
                        "∈"
                        (Order.Basic.«term_⊓_»
                         (Order.Basic.«term_⊓_»
                          (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                          " ⊓ "
                          (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                         " ⊓ "
                         (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
                      []
                      ")")]
                    []
                    ","
                    («term_=_»
                     (Term.typeAscription
                      "("
                      (Term.app
                       `Localization.mk
                       [`a1
                        (Term.anonymousCtor
                         "⟨"
                         [`b1
                          ","
                          (Term.show
                           "show"
                           («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.«tactic_<;>_»
                                (Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule
                                    [(patternIgnore (token.«← » "←"))]
                                    `ProjectiveSpectrum.mem_basic_open)]
                                  "]")
                                 [])
                                "<;>"
                                (Tactic.exact
                                 "exact"
                                 (Term.app
                                  `le_of_hom
                                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                    " ≫ "
                                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                                   `hy])))]))))]
                         "⟩")])
                      ":"
                      [(Term.app
                        `Localization.AtPrime
                        [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
                      ")")
                     "="
                     (Term.app
                      `Localization.mk
                      [`a2
                       (Term.anonymousCtor
                        "⟨"
                        [`b2
                         ","
                         (Term.show
                          "show"
                          («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                          (Term.byTactic'
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule
                                   [(patternIgnore (token.«← » "←"))]
                                   `ProjectiveSpectrum.mem_basic_open)]
                                 "]")
                                [])
                               "<;>"
                               (Tactic.exact
                                "exact"
                                (Term.app
                                 `le_of_hom
                                 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                   (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                   " ≫ "
                                   (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                                  `hy])))]))))]
                        "⟩")]))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.intro "intro" [`y `hy])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Localization.mk_eq_mk')
                        ","
                        (Tactic.rwRule [] `IsLocalization.eq)]
                       "]")
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor
                         "⟨"
                         [`c
                          ","
                          (Term.show
                           "show"
                           («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.«tactic_<;>_»
                                (Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule
                                    [(patternIgnore (token.«← » "←"))]
                                    `ProjectiveSpectrum.mem_basic_open)]
                                  "]")
                                 [])
                                "<;>"
                                (Tactic.exact
                                 "exact"
                                 (Term.app
                                  `le_of_hom
                                  [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                                   `hy])))]))))]
                         "⟩")
                        ","
                        `eq3]
                       "⟩"))]))))))
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                `presheaf.germ_ext
                [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
                 (Order.Basic.«term_⊓_»
                  (Order.Basic.«term_⊓_»
                   (Order.Basic.«term_⊓_»
                    (Order.Basic.«term_⊓_»
                     (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
                     " ⊓ "
                     (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
                    " ⊓ "
                    (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
                   " ⊓ "
                   `v1)
                  " ⊓ "
                  `v2)
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
                      "⟩")
                     ","
                     `memv1]
                    "⟩")
                   ","
                   `memv2]
                  "⟩")
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                   " ≫ "
                   `i1))
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  `i2)
                 (Term.hole "_")]))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]")
               [])
              []
              (Std.Tactic.Ext.tacticExt1___
               "ext1"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
              []
              (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"] [])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  `hs1
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.app
                      `le_of_hom
                      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                       (Term.proj `y "." (fieldIdx "2"))])]
                    "⟩")])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  `hs2
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.app
                      `le_of_hom
                      [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                       (Term.proj `y "." (fieldIdx "2"))])]
                    "⟩")])]])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               []
               [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `eq6)
                 ","
                 (Tactic.rwRule [] `eq7)
                 ","
                 (Tactic.rwRule [] `Quotient.eq)]
                "]")
               [])
              []
              (Tactic.change
               "change"
               («term_=_»
                (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
                "="
                (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `eq3'
                [(Term.hole "_")
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.app
                      `le_of_hom
                      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                         " ≫ "
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
                       (Term.proj `y "." (fieldIdx "2"))])
                     ","
                     (Term.app
                      `le_of_hom
                      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                         " ≫ "
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                          " ≫ "
                          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
                       (Term.proj `y "." (fieldIdx "2"))])]
                    "⟩")
                   ","
                   (Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                       " ≫ "
                       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
                     (Term.proj `y "." (fieldIdx "2"))])]
                  "⟩")]))])))))
        ","
        (Term.app
         (Term.proj `Function.surjective_iff_hasRightInverse "." `mpr)
         [(Term.anonymousCtor
           "⟨"
           [(Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [`f]
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
                    [(Tactic.rwRule [] `homogeneous_localization_to_stalk)]
                    "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.app
                       `stalk_to_fiber_ring_hom_germ
                       [`𝒜
                        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                        (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                        (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `section_in_basic_open)
                     ","
                     (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
                     ","
                     (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
                     ","
                     (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
                     ","
                     (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
                    "]"]
                   [])
                  []
                  (Tactic.tacticRfl "rfl")])))))]
           "⟩")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Function.surjective_iff_hasRightInverse "." `mpr)
       [(Term.anonymousCtor
         "⟨"
         [(Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `homogeneous_localization_to_stalk)] "]")
                 [])
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app
                     `stalk_to_fiber_ring_hom_germ
                     [`𝒜
                      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                      (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                      (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
                  "]")
                 [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `section_in_basic_open)
                   ","
                   (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
                   ","
                   (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
                   ","
                   (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
                   ","
                   (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
                  "]"]
                 [])
                []
                (Tactic.tacticRfl "rfl")])))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `homogeneous_localization_to_stalk)] "]")
               [])
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.app
                   `stalk_to_fiber_ring_hom_germ
                   [`𝒜
                    (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                    (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                    (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `section_in_basic_open)
                 ","
                 (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
                 ","
                 (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
                 ","
                 (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
                 ","
                 (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
                "]"]
               [])
              []
              (Tactic.tacticRfl "rfl")])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `homogeneous_localization_to_stalk)] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `stalk_to_fiber_ring_hom_germ
                 [`𝒜
                  (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                  (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                  (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `section_in_basic_open)
               ","
               (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
               ","
               (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
               ","
               (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
               ","
               (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
              "]"]
             [])
            []
            (Tactic.tacticRfl "rfl")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `homogeneous_localization_to_stalk)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `stalk_to_fiber_ring_hom_germ
               [`𝒜
                (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
                (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
                (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `section_in_basic_open)
             ","
             (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
             ","
             (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
             ","
             (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
             ","
             (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
            "]"]
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `section_in_basic_open)
         ","
         (Tactic.simpLemma [] [] `Subtype.ext_iff_val)
         ","
         (Tactic.simpLemma [] [] `HomogeneousLocalization.ext_iff_val)
         ","
         (Tactic.simpLemma [] [] `HomogeneousLocalization.val_mk')
         ","
         (Tactic.simpLemma [] [] `f.eq_num_div_denom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.eq_num_div_denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HomogeneousLocalization.val_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HomogeneousLocalization.ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `section_in_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `stalk_to_fiber_ring_hom_germ
           [`𝒜
            (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
            (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
            (Term.app `section_in_basic_open [(Term.hole "_") `x `f])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `stalk_to_fiber_ring_hom_germ
       [`𝒜
        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
        (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
        (Term.app `section_in_basic_open [(Term.hole "_") `x `f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `section_in_basic_open [(Term.hole "_") `x `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `section_in_basic_open
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `section_in_basic_open [(Term.hole "_") `x `f])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.denom
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `f.denom])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stalk_to_fiber_ring_hom_germ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `homogeneous_localization_to_stalk)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `homogeneous_localization_to_stalk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `homogeneousLocalizationToStalk [`𝒜 `x])
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
      `homogeneousLocalizationToStalk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Function.surjective_iff_hasRightInverse "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Function.surjective_iff_hasRightInverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z1 `z2 `eq1]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                (Term.proj
                 (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                 "."
                 `germ_exist)
                [`x `z1])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                (Term.proj
                 (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
                 "."
                 `germ_exist)
                [`x `z2])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j1)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
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
                              [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
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
                              [(Std.Tactic.RCases.rcasesPat.one `b1)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                (Term.proj `s1 "." (fieldIdx "2"))
                [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                              [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
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
                              [(Std.Tactic.RCases.rcasesPat.one `b2)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                (Term.proj `s2 "." (fieldIdx "2"))
                [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `stalk_to_fiber_ring_hom_germ
                 [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `stalk_to_fiber_ring_hom_germ
                 [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
              "="
              (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
             [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Localization.mk_eq_mk') "," (Tactic.rwRule [] `IsLocalization.eq)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                   [])]
                 "⟩")])]
             []
             [":=" [`eq3]])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq3' []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.explicitBinder
                    "("
                    [`y]
                    [":" (Term.app `ProjectiveSpectrum.top [`𝒜])]
                    []
                    ")")
                   (Term.explicitBinder
                    "("
                    [`hy]
                    [":"
                     («term_∈_»
                      `y
                      "∈"
                      (Order.Basic.«term_⊓_»
                       (Order.Basic.«term_⊓_»
                        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                        " ⊓ "
                        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                       " ⊓ "
                       (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
                    []
                    ")")]
                  []
                  ","
                  («term_=_»
                   (Term.typeAscription
                    "("
                    (Term.app
                     `Localization.mk
                     [`a1
                      (Term.anonymousCtor
                       "⟨"
                       [`b1
                        ","
                        (Term.show
                         "show"
                         («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule
                                  [(patternIgnore (token.«← » "←"))]
                                  `ProjectiveSpectrum.mem_basic_open)]
                                "]")
                               [])
                              "<;>"
                              (Tactic.exact
                               "exact"
                               (Term.app
                                `le_of_hom
                                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                  " ≫ "
                                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                                 `hy])))]))))]
                       "⟩")])
                    ":"
                    [(Term.app
                      `Localization.AtPrime
                      [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
                    ")")
                   "="
                   (Term.app
                    `Localization.mk
                    [`a2
                     (Term.anonymousCtor
                      "⟨"
                      [`b2
                       ","
                       (Term.show
                        "show"
                        («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                        (Term.byTactic'
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.«tactic_<;>_»
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule
                                 [(patternIgnore (token.«← » "←"))]
                                 `ProjectiveSpectrum.mem_basic_open)]
                               "]")
                              [])
                             "<;>"
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `le_of_hom
                               [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                 " ≫ "
                                 (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                                `hy])))]))))]
                      "⟩")]))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.intro "intro" [`y `hy])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `Localization.mk_eq_mk')
                      ","
                      (Tactic.rwRule [] `IsLocalization.eq)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [`c
                        ","
                        (Term.show
                         "show"
                         («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule
                                  [(patternIgnore (token.«← » "←"))]
                                  `ProjectiveSpectrum.mem_basic_open)]
                                "]")
                               [])
                              "<;>"
                              (Tactic.exact
                               "exact"
                               (Term.app
                                `le_of_hom
                                [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                                 `hy])))]))))]
                       "⟩")
                      ","
                      `eq3]
                     "⟩"))]))))))
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `presheaf.germ_ext
              [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
               (Order.Basic.«term_⊓_»
                (Order.Basic.«term_⊓_»
                 (Order.Basic.«term_⊓_»
                  (Order.Basic.«term_⊓_»
                   (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
                   " ⊓ "
                   (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
                  " ⊓ "
                  (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
                 " ⊓ "
                 `v1)
                " ⊓ "
                `v2)
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
                    "⟩")
                   ","
                   `memv1]
                  "⟩")
                 ","
                 `memv2]
                "⟩")
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 `i1))
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                `i2)
               (Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]")
             [])
            []
            (Std.Tactic.Ext.tacticExt1___
             "ext1"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
            []
            (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"] [])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                `hs1
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.hole "_")
                   ","
                   (Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                     (Term.proj `y "." (fieldIdx "2"))])]
                  "⟩")])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                `hs2
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.hole "_")
                   ","
                   (Term.app
                    `le_of_hom
                    [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                     (Term.proj `y "." (fieldIdx "2"))])]
                  "⟩")])]])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `eq6)
               ","
               (Tactic.rwRule [] `eq7)
               ","
               (Tactic.rwRule [] `Quotient.eq)]
              "]")
             [])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
              "="
              (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `eq3'
              [(Term.hole "_")
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
                     (Term.proj `y "." (fieldIdx "2"))])
                   ","
                   (Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
                     (Term.proj `y "." (fieldIdx "2"))])]
                  "⟩")
                 ","
                 (Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
                   (Term.proj `y "." (fieldIdx "2"))])]
                "⟩")]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj
               (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
               "."
               `germ_exist)
              [`x `z1])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj
               (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
               "."
               `germ_exist)
              [`x `z2])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j1)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                      [])]
                    "⟩")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj `s1 "." (fieldIdx "2"))
              [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                            [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                      [])]
                    "⟩")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj `s2 "." (fieldIdx "2"))
              [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           []
           [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `stalk_to_fiber_ring_hom_germ
               [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `stalk_to_fiber_ring_hom_germ
               [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
            "="
            (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
           [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Localization.mk_eq_mk') "," (Tactic.rwRule [] `IsLocalization.eq)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                      [])]
                    "⟩")])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
                 [])]
               "⟩")])]
           []
           [":=" [`eq3]])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq3' []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.explicitBinder "(" [`y] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")
                 (Term.explicitBinder
                  "("
                  [`hy]
                  [":"
                   («term_∈_»
                    `y
                    "∈"
                    (Order.Basic.«term_⊓_»
                     (Order.Basic.«term_⊓_»
                      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                      " ⊓ "
                      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                     " ⊓ "
                     (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
                  []
                  ")")]
                []
                ","
                («term_=_»
                 (Term.typeAscription
                  "("
                  (Term.app
                   `Localization.mk
                   [`a1
                    (Term.anonymousCtor
                     "⟨"
                     [`b1
                      ","
                      (Term.show
                       "show"
                       («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule
                                [(patternIgnore (token.«← » "←"))]
                                `ProjectiveSpectrum.mem_basic_open)]
                              "]")
                             [])
                            "<;>"
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `le_of_hom
                              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                                " ≫ "
                                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                               `hy])))]))))]
                     "⟩")])
                  ":"
                  [(Term.app
                    `Localization.AtPrime
                    [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
                  ")")
                 "="
                 (Term.app
                  `Localization.mk
                  [`a2
                   (Term.anonymousCtor
                    "⟨"
                    [`b2
                     ","
                     (Term.show
                      "show"
                      («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule
                               [(patternIgnore (token.«← » "←"))]
                               `ProjectiveSpectrum.mem_basic_open)]
                             "]")
                            [])
                           "<;>"
                           (Tactic.exact
                            "exact"
                            (Term.app
                             `le_of_hom
                             [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                               " ≫ "
                               (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                              `hy])))]))))]
                    "⟩")]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`y `hy])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Localization.mk_eq_mk')
                    ","
                    (Tactic.rwRule [] `IsLocalization.eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.anonymousCtor
                     "⟨"
                     [`c
                      ","
                      (Term.show
                       "show"
                       («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule
                                [(patternIgnore (token.«← » "←"))]
                                `ProjectiveSpectrum.mem_basic_open)]
                              "]")
                             [])
                            "<;>"
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `le_of_hom
                              [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                               `hy])))]))))]
                     "⟩")
                    ","
                    `eq3]
                   "⟩"))]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `presheaf.germ_ext
            [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
             (Order.Basic.«term_⊓_»
              (Order.Basic.«term_⊓_»
               (Order.Basic.«term_⊓_»
                (Order.Basic.«term_⊓_»
                 (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
                 " ⊓ "
                 (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
                " ⊓ "
                (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
               " ⊓ "
               `v1)
              " ⊓ "
              `v2)
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
                  "⟩")
                 ","
                 `memv1]
                "⟩")
               ","
               `memv2]
              "⟩")
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               `i1))
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              `i2)
             (Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]")
           [])
          []
          (Std.Tactic.Ext.tacticExt1___
           "ext1"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"] [])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `hs1
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                   (Term.proj `y "." (fieldIdx "2"))])]
                "⟩")])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `hs2
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.app
                  `le_of_hom
                  [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                   (Term.proj `y "." (fieldIdx "2"))])]
                "⟩")])]])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           []
           [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `eq6)
             ","
             (Tactic.rwRule [] `eq7)
             ","
             (Tactic.rwRule [] `Quotient.eq)]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
            "="
            (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `eq3'
            [(Term.hole "_")
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
                   (Term.proj `y "." (fieldIdx "2"))])
                 ","
                 (Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
                   (Term.proj `y "." (fieldIdx "2"))])]
                "⟩")
               ","
               (Term.app
                `le_of_hom
                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                   " ≫ "
                   (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
                 (Term.proj `y "." (fieldIdx "2"))])]
              "⟩")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `eq3'
        [(Term.hole "_")
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.app
              `le_of_hom
              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
               (Term.proj `y "." (fieldIdx "2"))])
             ","
             (Term.app
              `le_of_hom
              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
               (Term.proj `y "." (fieldIdx "2"))])]
            "⟩")
           ","
           (Term.app
            `le_of_hom
            [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
             (Term.proj `y "." (fieldIdx "2"))])]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eq3'
       [(Term.hole "_")
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.app
             `le_of_hom
             [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
              (Term.proj `y "." (fieldIdx "2"))])
            ","
            (Term.app
             `le_of_hom
             [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                 " ≫ "
                 (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
              (Term.proj `y "." (fieldIdx "2"))])]
           "⟩")
          ","
          (Term.app
           `le_of_hom
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
            (Term.proj `y "." (fieldIdx "2"))])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.app
           `le_of_hom
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
            (Term.proj `y "." (fieldIdx "2"))])
          ","
          (Term.app
           `le_of_hom
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
               " ≫ "
               (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
            (Term.proj `y "." (fieldIdx "2"))])]
         "⟩")
        ","
        (Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
            " ≫ "
            (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
          (Term.proj `y "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
        (Term.proj `y "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
            " ≫ "
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
          (Term.proj `y "." (fieldIdx "2"))])
        ","
        (Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
            " ≫ "
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
          (Term.proj `y "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
        (Term.proj `y "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
        (Term.proj `y "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq3'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
        "="
        (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
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
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
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
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `eq6) "," (Tactic.rwRule [] `eq7) "," (Tactic.rwRule [] `Quotient.eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq7
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq6
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       []
       [(Tactic.location "at" (Tactic.locationHyp [`eq6 `eq7] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq7
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq6
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq7)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `hs2
          [(Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.app
              `le_of_hom
              [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
               (Term.proj `y "." (fieldIdx "2"))])]
            "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hs2
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.app
           `le_of_hom
           [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
            (Term.proj `y "." (fieldIdx "2"))])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app
         `le_of_hom
         [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
          (Term.proj `y "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
        (Term.proj `y "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq6)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `hs1
          [(Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.app
              `le_of_hom
              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
               (Term.proj `y "." (fieldIdx "2"))])]
            "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hs1
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.app
           `le_of_hom
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
            (Term.proj `y "." (fieldIdx "2"))])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
          (Term.proj `y "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
        (Term.proj `y "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `res_apply)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `res_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.ext_iff_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `presheaf.germ_ext
        [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
         (Order.Basic.«term_⊓_»
          (Order.Basic.«term_⊓_»
           (Order.Basic.«term_⊓_»
            (Order.Basic.«term_⊓_»
             (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
             " ⊓ "
             (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
            " ⊓ "
            (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
           " ⊓ "
           `v1)
          " ⊓ "
          `v2)
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
              "⟩")
             ","
             `memv1]
            "⟩")
           ","
           `memv2]
          "⟩")
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           `i1))
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          `i2)
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `presheaf.germ_ext
       [(Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
        (Order.Basic.«term_⊓_»
         (Order.Basic.«term_⊓_»
          (Order.Basic.«term_⊓_»
           (Order.Basic.«term_⊓_»
            (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
            " ⊓ "
            (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
           " ⊓ "
           (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
          " ⊓ "
          `v1)
         " ⊓ "
         `v2)
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
             "⟩")
            ","
            `memv1]
           "⟩")
          ","
          `memv2]
         "⟩")
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          `i1))
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         `i2)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       `i2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i2
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      `i2)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        `i1))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       `i1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i1
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       `i1))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
           "⟩")
          ","
          `memv1]
         "⟩")
        ","
        `memv2]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memv2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc]
         "⟩")
        ","
        `memv1]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memv1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩") "," `hc] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b1_nin_x "," `b2_nin_x] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b2_nin_x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1_nin_x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_⊓_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_⊓_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_⊓_»
       (Order.Basic.«term_⊓_»
        (Order.Basic.«term_⊓_»
         (Order.Basic.«term_⊓_»
          (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
          " ⊓ "
          (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
         " ⊓ "
         (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
        " ⊓ "
        `v1)
       " ⊓ "
       `v2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v2
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Order.Basic.«term_⊓_»
       (Order.Basic.«term_⊓_»
        (Order.Basic.«term_⊓_»
         (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
         " ⊓ "
         (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
        " ⊓ "
        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
       " ⊓ "
       `v1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v1
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Order.Basic.«term_⊓_»
       (Order.Basic.«term_⊓_»
        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
        " ⊓ "
        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
       " ⊓ "
       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Order.Basic.«term_⊓_»
       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
       " ⊓ "
       (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1022, (some 1023, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 69, (some 70, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 69, (some 70, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 69, (some 70, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 69, (some 70, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Order.Basic.«term_⊓_»
      (Order.Basic.«term_⊓_»
       (Order.Basic.«term_⊓_»
        (Order.Basic.«term_⊓_»
         (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b1])
         " ⊓ "
         (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `b2]))
        " ⊓ "
        (Term.app `ProjectiveSpectrum.basicOpen [(Term.hole "_") `c]))
       " ⊓ "
       `v1)
      " ⊓ "
      `v2)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Proj.structure_sheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Proj.structure_sheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Proj.structure_sheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `presheaf.germ_ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`eq3' []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.explicitBinder "(" [`y] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")
             (Term.explicitBinder
              "("
              [`hy]
              [":"
               («term_∈_»
                `y
                "∈"
                (Order.Basic.«term_⊓_»
                 (Order.Basic.«term_⊓_»
                  (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
                  " ⊓ "
                  (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
                 " ⊓ "
                 (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
              []
              ")")]
            []
            ","
            («term_=_»
             (Term.typeAscription
              "("
              (Term.app
               `Localization.mk
               [`a1
                (Term.anonymousCtor
                 "⟨"
                 [`b1
                  ","
                  (Term.show
                   "show"
                   («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            `ProjectiveSpectrum.mem_basic_open)]
                          "]")
                         [])
                        "<;>"
                        (Tactic.exact
                         "exact"
                         (Term.app
                          `le_of_hom
                          [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                            " ≫ "
                            (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                           `hy])))]))))]
                 "⟩")])
              ":"
              [(Term.app
                `Localization.AtPrime
                [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
              ")")
             "="
             (Term.app
              `Localization.mk
              [`a2
               (Term.anonymousCtor
                "⟨"
                [`b2
                 ","
                 (Term.show
                  "show"
                  («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
                  (Term.byTactic'
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           `ProjectiveSpectrum.mem_basic_open)]
                         "]")
                        [])
                       "<;>"
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `le_of_hom
                         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                           " ≫ "
                           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                          `hy])))]))))]
                "⟩")]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`y `hy])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Localization.mk_eq_mk')
                ","
                (Tactic.rwRule [] `IsLocalization.eq)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [`c
                  ","
                  (Term.show
                   "show"
                   («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            `ProjectiveSpectrum.mem_basic_open)]
                          "]")
                         [])
                        "<;>"
                        (Tactic.exact
                         "exact"
                         (Term.app
                          `le_of_hom
                          [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                           `hy])))]))))]
                 "⟩")
                ","
                `eq3]
               "⟩"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`y `hy])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Localization.mk_eq_mk') "," (Tactic.rwRule [] `IsLocalization.eq)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [`c
               ","
               (Term.show
                "show"
                («term_∉_» `c "∉" `y.as_homogeneous_ideal)
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         `ProjectiveSpectrum.mem_basic_open)]
                       "]")
                      [])
                     "<;>"
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `le_of_hom
                       [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
                        `hy])))]))))]
              "⟩")
             ","
             `eq3]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [`c
           ","
           (Term.show
            "show"
            («term_∉_» `c "∉" `y.as_homogeneous_ideal)
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     `ProjectiveSpectrum.mem_basic_open)]
                   "]")
                  [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `le_of_hom
                   [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])))]))))]
          "⟩")
         ","
         `eq3]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [`c
          ","
          (Term.show
           "show"
           («term_∉_» `c "∉" `y.as_homogeneous_ideal)
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    `ProjectiveSpectrum.mem_basic_open)]
                  "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.app
                  `le_of_hom
                  [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])))]))))]
         "⟩")
        ","
        `eq3]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`c
        ","
        (Term.show
         "show"
         («term_∉_» `c "∉" `y.as_homogeneous_ideal)
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  `ProjectiveSpectrum.mem_basic_open)]
                "]")
               [])
              "<;>"
              (Tactic.exact
               "exact"
               (Term.app
                `le_of_hom
                [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])))]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∉_» `c "∉" `y.as_homogeneous_ideal)
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                `ProjectiveSpectrum.mem_basic_open)]
              "]")
             [])
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `le_of_hom
              [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `le_of_hom
         [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `le_of_hom [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_hom [(Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]) `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∉_» `c "∉" `y.as_homogeneous_ideal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.as_homogeneous_ideal
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
        [(Tactic.rwRule [] `Localization.mk_eq_mk') "," (Tactic.rwRule [] `IsLocalization.eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsLocalization.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_eq_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`y `hy])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`y] [":" (Term.app `ProjectiveSpectrum.top [`𝒜])] [] ")")
        (Term.explicitBinder
         "("
         [`hy]
         [":"
          («term_∈_»
           `y
           "∈"
           (Order.Basic.«term_⊓_»
            (Order.Basic.«term_⊓_»
             (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
             " ⊓ "
             (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
            " ⊓ "
            (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))]
         []
         ")")]
       []
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app
          `Localization.mk
          [`a1
           (Term.anonymousCtor
            "⟨"
            [`b1
             ","
             (Term.show
              "show"
              («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       `ProjectiveSpectrum.mem_basic_open)]
                     "]")
                    [])
                   "<;>"
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `le_of_hom
                     [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                       " ≫ "
                       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                      `hy])))]))))]
            "⟩")])
         ":"
         [(Term.app
           `Localization.AtPrime
           [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
         ")")
        "="
        (Term.app
         `Localization.mk
         [`a2
          (Term.anonymousCtor
           "⟨"
           [`b2
            ","
            (Term.show
             "show"
             («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `ProjectiveSpectrum.mem_basic_open)]
                    "]")
                   [])
                  "<;>"
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                     `hy])))]))))]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app
         `Localization.mk
         [`a1
          (Term.anonymousCtor
           "⟨"
           [`b1
            ","
            (Term.show
             "show"
             («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `ProjectiveSpectrum.mem_basic_open)]
                    "]")
                   [])
                  "<;>"
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `le_of_hom
                    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                      " ≫ "
                      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                     `hy])))]))))]
           "⟩")])
        ":"
        [(Term.app
          `Localization.AtPrime
          [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
        ")")
       "="
       (Term.app
        `Localization.mk
        [`a2
         (Term.anonymousCtor
          "⟨"
          [`b2
           ","
           (Term.show
            "show"
            («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     `ProjectiveSpectrum.mem_basic_open)]
                   "]")
                  [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `le_of_hom
                   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                    `hy])))]))))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Localization.mk
       [`a2
        (Term.anonymousCtor
         "⟨"
         [`b2
          ","
          (Term.show
           "show"
           («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    `ProjectiveSpectrum.mem_basic_open)]
                  "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                   `hy])))]))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`b2
        ","
        (Term.show
         "show"
         («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  `ProjectiveSpectrum.mem_basic_open)]
                "]")
               [])
              "<;>"
              (Tactic.exact
               "exact"
               (Term.app
                `le_of_hom
                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
                 `hy])))]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                `ProjectiveSpectrum.mem_basic_open)]
              "]")
             [])
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `le_of_hom
              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
               `hy])))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
          `hy])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_of_hom
        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
         `hy]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
        `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (Term.app `opens.inf_le_right [(Term.hole "_") (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∉_» `b2 "∉" (Term.proj `y "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b2
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app
        `Localization.mk
        [`a1
         (Term.anonymousCtor
          "⟨"
          [`b1
           ","
           (Term.show
            "show"
            («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     `ProjectiveSpectrum.mem_basic_open)]
                   "]")
                  [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `le_of_hom
                   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                    `hy])))]))))]
          "⟩")])
       ":"
       [(Term.app
         `Localization.AtPrime
         [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.AtPrime [(Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `y "." (fieldIdx "1")) "." `toIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.AtPrime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Localization.mk
       [`a1
        (Term.anonymousCtor
         "⟨"
         [`b1
          ","
          (Term.show
           "show"
           («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    `ProjectiveSpectrum.mem_basic_open)]
                  "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.app
                  `le_of_hom
                  [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                    " ≫ "
                    (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                   `hy])))]))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`b1
        ","
        (Term.show
         "show"
         («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  `ProjectiveSpectrum.mem_basic_open)]
                "]")
               [])
              "<;>"
              (Tactic.exact
               "exact"
               (Term.app
                `le_of_hom
                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
                 `hy])))]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                `ProjectiveSpectrum.mem_basic_open)]
              "]")
             [])
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `le_of_hom
              [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
                " ≫ "
                (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
               `hy])))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `le_of_hom
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
           " ≫ "
           (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
          `hy])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_of_hom
        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
          " ≫ "
          (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
         `hy]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_hom
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
        `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
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
      `opens.inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")])
      " ≫ "
      (Term.app `opens.inf_le_left [(Term.hole "_") (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ProjectiveSpectrum.mem_basic_open)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ProjectiveSpectrum.mem_basic_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∉_» `b1 "∉" (Term.proj `y "." `asHomogeneousIdeal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." `asHomogeneousIdeal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `y
       "∈"
       (Order.Basic.«term_⊓_»
        (Order.Basic.«term_⊓_»
         (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
         " ⊓ "
         (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
        " ⊓ "
        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_»
       (Order.Basic.«term_⊓_»
        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
        " ⊓ "
        (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
       " ⊓ "
       (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Order.Basic.«term_⊓_»
       (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
       " ⊓ "
       (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Term.app `ProjectiveSpectrum.basicOpen [`𝒜 `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.basicOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1022, (some 1023, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 69, (some 70, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 69, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ProjectiveSpectrum.top [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ProjectiveSpectrum.top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                  [])]
                "⟩")])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
             [])]
           "⟩")])]
       []
       [":=" [`eq3]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Localization.mk_eq_mk') "," (Tactic.rwRule [] `IsLocalization.eq)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsLocalization.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Localization.mk_eq_mk'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
        "="
        (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
       [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
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
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Localization.mk [(Term.hole "_") (Term.hole "_")])
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
      `Localization.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq2) "," (Tactic.rwRule [] `Quotient.eq)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq3] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq1)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq2] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `stalk_to_fiber_ring_hom_germ
           [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `stalk_to_fiber_ring_hom_germ
           [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`eq1] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `stalk_to_fiber_ring_hom_germ
       [`𝒜 `u2 (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩") `s2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memu2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `u2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stalk_to_fiber_ring_hom_germ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `stalk_to_fiber_ring_hom_germ
       [`𝒜 `u1 (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩") `s1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memu1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `u1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stalk_to_fiber_ring_hom_germ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       []
       [(Tactic.location "at" (Tactic.locationHyp [`eq1 `eq2 `eq3] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_nin_x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq3)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hs2 [(Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `memv2] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memv2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_nin_x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq2)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hs1 [(Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `memv1] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memv1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j2)])
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a2_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b2_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs2)])
                  [])]
                "⟩")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj `s2 "." (fieldIdx "2"))
          [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s2 "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `memu2] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memu2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `s2 "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memv1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j1)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a1_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b1_mem)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs1)])
                  [])]
                "⟩")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj `s1 "." (fieldIdx "2"))
          [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s1 "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `memu1] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `memu1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `s1 "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s2)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj
           (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
           "."
           `germ_exist)
          [`x `z2])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf) "." `germ_exist)
       [`x `z2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf) "." `germ_exist)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Proj.structure_sheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Proj.structure_sheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Proj.structure_sheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `memu1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s1)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj
           (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
           "."
           `germ_exist)
          [`x `z1])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf) "." `germ_exist)
       [`x `z1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf) "." `germ_exist)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Proj.structure_sheaf [`𝒜]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Proj.structure_sheaf [`𝒜])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝒜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Proj.structure_sheaf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Proj.structure_sheaf [`𝒜])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `stalkToFiberRingHom [(Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stalkToFiberRingHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `stalkToFiberRingHom [(Term.hole "_") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingEquiv.ofBijective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Ring.Equiv.«term_≃+*_»
       (Term.app
        (Term.proj (Term.proj (Term.app `ProjCat.structureSheaf [`𝒜]) "." `Presheaf) "." `stalk)
        [`x])
       " ≃+* "
       (Term.app
        `CommRingCat.of
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `CommRingCat.of
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Using `homogeneous_localization_to_stalk`, we construct a ring isomorphism between stalk at `x`
    and homogeneous localization at `x` for any point `x` in `Proj`.-/
  def
    ProjCat.stalkIso'
    ( x : ProjectiveSpectrum.top 𝒜 )
      : ProjCat.structureSheaf 𝒜 . Presheaf . stalk x ≃+* CommRingCat.of at x
    :=
      RingEquiv.ofBijective
        stalkToFiberRingHom _ x
          ⟨
            fun
                z1 z2 eq1
                  =>
                  by
                    obtain
                        ⟨ u1 , memu1 , s1 , rfl ⟩
                        := Proj.structure_sheaf 𝒜 . Presheaf . germ_exist x z1
                      obtain
                        ⟨ u2 , memu2 , s2 , rfl ⟩
                        := Proj.structure_sheaf 𝒜 . Presheaf . germ_exist x z2
                      obtain
                        ⟨ v1 , memv1 , i1 , ⟨ j1 , ⟨ a1 , a1_mem ⟩ , ⟨ b1 , b1_mem ⟩ , hs1 ⟩ ⟩
                        := s1 . 2 ⟨ x , memu1 ⟩
                      obtain
                        ⟨ v2 , memv2 , i2 , ⟨ j2 , ⟨ a2 , a2_mem ⟩ , ⟨ b2 , b2_mem ⟩ , hs2 ⟩ ⟩
                        := s2 . 2 ⟨ x , memu2 ⟩
                      obtain ⟨ b1_nin_x , eq2 ⟩ := hs1 ⟨ x , memv1 ⟩
                      obtain ⟨ b2_nin_x , eq3 ⟩ := hs2 ⟨ x , memv2 ⟩
                      dsimp only at eq1 eq2 eq3
                      erw
                        [
                          stalk_to_fiber_ring_hom_germ 𝒜 u1 ⟨ x , memu1 ⟩ s1
                            ,
                            stalk_to_fiber_ring_hom_germ 𝒜 u2 ⟨ x , memu2 ⟩ s2
                          ]
                        at eq1
                      erw [ eq1 ] at eq2
                      erw [ eq2 , Quotient.eq ] at eq3
                      change Localization.mk _ _ = Localization.mk _ _ at eq3
                      rw [ Localization.mk_eq_mk' , IsLocalization.eq ] at eq3
                      obtain ⟨ ⟨ c , hc ⟩ , eq3 ⟩ := eq3
                      simp only [ ← Subtype.val_eq_coe ] at eq3
                      have
                        eq3'
                          :
                            ∀
                              ( y : ProjectiveSpectrum.top 𝒜 )
                                (
                                  hy
                                  :
                                    y
                                      ∈
                                      ProjectiveSpectrum.basicOpen 𝒜 b1
                                          ⊓
                                          ProjectiveSpectrum.basicOpen 𝒜 b2
                                        ⊓
                                        ProjectiveSpectrum.basicOpen 𝒜 c
                                  )
                              ,
                              (
                                  Localization.mk
                                    a1
                                      ⟨
                                        b1
                                          ,
                                          show
                                            b1 ∉ y . asHomogeneousIdeal
                                            by
                                              rw [ ← ProjectiveSpectrum.mem_basic_open ]
                                                <;>
                                                exact
                                                  le_of_hom
                                                    opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ hy
                                        ⟩
                                  :
                                  Localization.AtPrime y . 1 . toIdeal
                                  )
                                =
                                Localization.mk
                                  a2
                                    ⟨
                                      b2
                                        ,
                                        show
                                          b2 ∉ y . asHomogeneousIdeal
                                          by
                                            rw [ ← ProjectiveSpectrum.mem_basic_open ]
                                              <;>
                                              exact
                                                le_of_hom
                                                  opens.inf_le_left _ _ ≫ opens.inf_le_right _ _ hy
                                      ⟩
                          :=
                          by
                            intro y hy
                              rw [ Localization.mk_eq_mk' , IsLocalization.eq ]
                              exact
                                ⟨
                                  ⟨
                                      c
                                        ,
                                        show
                                          c ∉ y.as_homogeneous_ideal
                                          by
                                            rw [ ← ProjectiveSpectrum.mem_basic_open ]
                                              <;>
                                              exact le_of_hom opens.inf_le_right _ _ hy
                                      ⟩
                                    ,
                                    eq3
                                  ⟩
                      refine'
                        presheaf.germ_ext
                          Proj.structure_sheaf 𝒜 . 1
                            ProjectiveSpectrum.basicOpen _ b1 ⊓ ProjectiveSpectrum.basicOpen _ b2
                                  ⊓
                                  ProjectiveSpectrum.basicOpen _ c
                                ⊓
                                v1
                              ⊓
                              v2
                            ⟨ ⟨ ⟨ ⟨ b1_nin_x , b2_nin_x ⟩ , hc ⟩ , memv1 ⟩ , memv2 ⟩
                            opens.inf_le_left _ _ ≫ opens.inf_le_right _ _ ≫ i1
                            opens.inf_le_right _ _ ≫ i2
                            _
                      rw [ Subtype.ext_iff_val ]
                      ext1 y
                      simp only [ res_apply ]
                      obtain
                        ⟨ b1_nin_y , eq6 ⟩
                        :=
                          hs1 ⟨ _ , le_of_hom opens.inf_le_left _ _ ≫ opens.inf_le_right _ _ y . 2 ⟩
                      obtain
                        ⟨ b2_nin_y , eq7 ⟩
                        := hs2 ⟨ _ , le_of_hom opens.inf_le_right _ _ y . 2 ⟩
                      simp only at eq6 eq7
                      erw [ eq6 , eq7 , Quotient.eq ]
                      change Localization.mk _ _ = Localization.mk _ _
                      exact
                        eq3'
                          _
                            ⟨
                              ⟨
                                  le_of_hom
                                      opens.inf_le_left _ _
                                          ≫
                                          opens.inf_le_left _ _
                                            ≫
                                            opens.inf_le_left _ _ ≫ opens.inf_le_left _ _
                                        y . 2
                                    ,
                                    le_of_hom
                                      opens.inf_le_left _ _
                                          ≫
                                          opens.inf_le_left _ _
                                            ≫
                                            opens.inf_le_left _ _ ≫ opens.inf_le_right _ _
                                        y . 2
                                  ⟩
                                ,
                                le_of_hom
                                  opens.inf_le_left _ _
                                      ≫
                                      opens.inf_le_left _ _ ≫ opens.inf_le_right _ _
                                    y . 2
                              ⟩
              ,
              Function.surjective_iff_hasRightInverse . mpr
                ⟨
                  homogeneousLocalizationToStalk 𝒜 x
                    ,
                    fun
                      f
                        =>
                        by
                          rw [ homogeneous_localization_to_stalk ]
                            erw
                              [
                                stalk_to_fiber_ring_hom_germ
                                  𝒜
                                    ProjectiveSpectrum.basicOpen 𝒜 f.denom
                                    ⟨ x , _ ⟩
                                    section_in_basic_open _ x f
                                ]
                            simp
                              only
                              [
                                section_in_basic_open
                                  ,
                                  Subtype.ext_iff_val
                                  ,
                                  HomogeneousLocalization.ext_iff_val
                                  ,
                                  HomogeneousLocalization.val_mk'
                                  ,
                                  f.eq_num_div_denom
                                ]
                            rfl
                  ⟩
            ⟩
#align algebraic_geometry.Proj.stalk_iso' AlgebraicGeometry.ProjCat.stalkIso'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "`Proj` of a graded ring as a `LocallyRingedSpace`-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ProjCat.toLocallyRingedSpace [])
      (Command.optDeclSig [] [(Term.typeSpec ":" `LocallyRingedSpaceCat)])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[(Term.app `ProjCat.toSheafedSpace [`𝒜])] "with"]
        [(Term.structInstField
          (Term.structInstLVal `LocalRing [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             (Term.explicit "@" `RingEquiv.local_ring)
             [(Term.hole "_")
              (Term.show
               "show"
               (Term.app
                `LocalRing
                [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
                  "at "
                  `x)])
               (Term.fromTerm "from" `inferInstance))
              (Term.hole "_")
              (Term.proj (Term.app `ProjCat.stalkIso' [`𝒜 `x]) "." `symm)]))))]
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
       [[(Term.app `ProjCat.toSheafedSpace [`𝒜])] "with"]
       [(Term.structInstField
         (Term.structInstLVal `LocalRing [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            (Term.explicit "@" `RingEquiv.local_ring)
            [(Term.hole "_")
             (Term.show
              "show"
              (Term.app
               `LocalRing
               [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
                 "at "
                 `x)])
              (Term.fromTerm "from" `inferInstance))
             (Term.hole "_")
             (Term.proj (Term.app `ProjCat.stalkIso' [`𝒜 `x]) "." `symm)]))))]
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
        (Term.app
         (Term.explicit "@" `RingEquiv.local_ring)
         [(Term.hole "_")
          (Term.show
           "show"
           (Term.app
            `LocalRing
            [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
              "at "
              `x)])
           (Term.fromTerm "from" `inferInstance))
          (Term.hole "_")
          (Term.proj (Term.app `ProjCat.stalkIso' [`𝒜 `x]) "." `symm)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `RingEquiv.local_ring)
       [(Term.hole "_")
        (Term.show
         "show"
         (Term.app
          `LocalRing
          [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_
            "at "
            `x)])
         (Term.fromTerm "from" `inferInstance))
        (Term.hole "_")
        (Term.proj (Term.app `ProjCat.stalkIso' [`𝒜 `x]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `ProjCat.stalkIso' [`𝒜 `x]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ProjCat.stalkIso' [`𝒜 `x])
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
      `ProjCat.stalkIso'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ProjCat.stalkIso' [`𝒜 `x])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.show
       "show"
       (Term.app
        `LocalRing
        [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `LocalRing
       [(AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_ "at " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_', expected 'AlgebraicGeometry.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.termat_._@.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/-- `Proj` of a graded ring as a `LocallyRingedSpace`-/
  def
    ProjCat.toLocallyRingedSpace
    : LocallyRingedSpaceCat
    :=
      {
        ProjCat.toSheafedSpace 𝒜 with
        LocalRing
          :=
          fun
            x
              =>
              @ RingEquiv.local_ring
                _ show LocalRing at x from inferInstance _ ProjCat.stalkIso' 𝒜 x . symm
        }
#align algebraic_geometry.Proj.to_LocallyRingedSpace AlgebraicGeometry.ProjCat.toLocallyRingedSpace

end

end AlgebraicGeometry

