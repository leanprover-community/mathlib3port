import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.Algebra.Homology.Single
import Mathbin.Algebra.Homology.HomotopyCategory

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.

When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory of derived functors
without even assuming `C` is abelian.

(Typically, however, to show `has_projective_resolutions C`
one will assume `enough_projectives C` and `abelian C`.
This construction appears in `category_theory.abelian.projectives`.)

We show that given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)

Moreover, we show that any two such lifts are homotopic.

As a consequence, if every object admits a projective resolution,
we can construct a functor `projective_resolutions C : C ⥤ homotopy_category C`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [category.{v} C]

open Projective

section

variable [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

/-- 
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

(We don't actually ask here that the chain map is a quasi-iso, just exactness everywhere:
that `π` is a quasi-iso is a lemma when the category is abelian.
Should we just ask for it here?)

Except in situations where you want to provide a particular projective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `projective_resolution Z`: the `ℕ`-indexed chain complex
  (equipped with `projective` and `exact` instances)
* `projective_resolution.π Z`: the chain map from `projective_resolution Z` to
  `(single C _ 0).obj Z` (all the components are equipped with `epi` instances,
  and when the category is `abelian` we will show `π` is a quasi-iso).
-/
@[nolint has_inhabited_instance]
structure ProjectiveResolution (Z : C) where
  complex : ChainComplex C ℕ
  π : HomologicalComplex.Hom complex ((ChainComplex.single₀ C).obj Z)
  Projective : ∀ n, projective (complex.X n) := by
    run_tac
      tactic.apply_instance
  exact₀ : exact (complex.d 1 0) (π.f 0) := by
    run_tac
      tactic.apply_instance
  exact : ∀ n, exact (complex.d (n+2) (n+1)) (complex.d (n+1) n) := by
    run_tac
      tactic.apply_instance
  Epi : epi (π.f 0) := by
    run_tac
      tactic.apply_instance

attribute [instance]
  ProjectiveResolution.projective ProjectiveResolution.exact₀ ProjectiveResolution.exact ProjectiveResolution.epi

/-- 
An object admits a projective resolution.
-/
class has_projective_resolution (Z : C) : Prop where
  out {} : Nonempty (ProjectiveResolution Z)

section

variable (C)

/-- 
You will rarely use this typeclass directly: it is implied by the combination
`[enough_projectives C]` and `[abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class has_projective_resolutions : Prop where
  out : ∀ Z : C, has_projective_resolution Z

attribute [instance] has_projective_resolutions.out

end

namespace ProjectiveResolution

@[simp]
theorem π_f_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : P.π.f (n+1) = 0 := by
  apply zero_of_target_iso_zero
  dsimp
  rfl

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : CategoryTheory.Epi (P.π.f n) := by
  cases n <;> infer_instance

/--  A projective object admits a trivial projective resolution: itself in degree 0. -/
def self (Z : C) [CategoryTheory.Projective Z] : ProjectiveResolution Z :=
  { complex := (ChainComplex.single₀ C).obj Z, π := 𝟙 ((ChainComplex.single₀ C).obj Z),
    Projective := fun n => by
      cases n
      ·
        dsimp
        infer_instance
      ·
        dsimp
        infer_instance,
    exact₀ := by
      dsimp
      infer_instance,
    exact := fun n => by
      dsimp
      infer_instance,
    Epi := by
      dsimp
      infer_instance }

/--  Auxiliary construction for `lift`. -/
def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  factor_thru (P.π.f 0 ≫ f) (Q.π.f 0)

/--  Auxiliary construction for `lift`. -/
def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  exact.lift (P.complex.d 1 0 ≫ lift_f_zero f P Q) (Q.complex.d 1 0) (Q.π.f 0)
    (by
      simp [lift_f_zero])

/--  Auxiliary lemma for `lift`. -/
@[simp]
theorem lift_f_one_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    lift_f_one f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ lift_f_zero f P Q := by
  dsimp [lift_f_zero, lift_f_one]
  simp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " Auxiliary construction for `lift`. -/")] [] [] [] [] [])
 (Command.def
  "def"
  (Command.declId `lift_f_succ [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`Y `Z] [":" `C] "}")
    (Term.explicitBinder "(" [`P] [":" (Term.app `ProjectiveResolution [`Y])] [] ")")
    (Term.explicitBinder "(" [`Q] [":" (Term.app `ProjectiveResolution [`Z])] [] ")")
    (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder
     "("
     [`g]
     [":" (Combinatorics.Quiver.«term_⟶_» (Term.app `P.complex.X [`n]) " ⟶ " (Term.app `Q.complex.X [`n]))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`g']
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (Term.app `P.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
       " ⟶ "
       (Term.app `Q.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`w]
     [":"
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `g'
        " ≫ "
        (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
        " ≫ "
        `g))]
     []
     ")")]
   [(Term.typeSpec
     ":"
     (Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `g'')]
        [":"
         (Combinatorics.Quiver.«term_⟶_»
          (Term.app `P.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
          " ⟶ "
          (Term.app `Q.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]))
      ", "
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `g''
        " ≫ "
        (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        " ≫ "
        `g'))))])
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(Term.app
      `exact.lift
      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        " ≫ "
        `g')
       (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] []) [])])))])
     ","
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
    "⟩")
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     `exact.lift
     [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       " ≫ "
       `g')
      (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] []) [])])))])
    ","
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `exact.lift
   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
     " ≫ "
     `g')
    (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `w)] "]"] []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.complex.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Q.complex.d [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")") `n]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.complex.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Q.complex.d
   [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
    (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   " ≫ "
   `g')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.complex.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app
    `P.complex.d
    [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
     (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")])
   " ≫ "
   `g')
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exact.lift
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `g'')]
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (Term.app `P.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
       " ⟶ "
       (Term.app `Q.complex.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]))
   ", "
   («term_=_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `g''
     " ≫ "
     (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
    "="
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
     " ≫ "
     `g')))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `g''
    " ≫ "
    (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
   "="
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    " ≫ "
    `g'))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   " ≫ "
   `g')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `P.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.complex.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `g''
   " ≫ "
   (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Q.complex.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.complex.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `g''
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Auxiliary construction for `lift`. -/
  def
    lift_f_succ
    { Y Z : C }
        ( P : ProjectiveResolution Y )
        ( Q : ProjectiveResolution Z )
        ( n : ℕ )
        ( g : P.complex.X n ⟶ Q.complex.X n )
        ( g' : P.complex.X n + 1 ⟶ Q.complex.X n + 1 )
        ( w : g' ≫ Q.complex.d n + 1 n = P.complex.d n + 1 n ≫ g )
      : Σ' g'' : P.complex.X n + 2 ⟶ Q.complex.X n + 2 , g'' ≫ Q.complex.d n + 2 n + 1 = P.complex.d n + 2 n + 1 ≫ g'
    := ⟨ exact.lift P.complex.d n + 2 n + 1 ≫ g' Q.complex.d n + 2 n + 1 Q.complex.d n + 1 n by simp [ w ] , by simp ⟩

/--  A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) : P.complex ⟶ Q.complex := by
  fapply ChainComplex.mkHom
  apply lift_f_zero f
  apply lift_f_one f
  apply lift_f_one_zero_comm f
  rintro n ⟨g, g', w⟩
  exact lift_f_succ P Q n g g' w

/--  The resolution maps interwine the lift of a morphism and that morphism. -/
@[simp, reassoc]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext n
  rcases n with (_ | _ | n)
  ·
    dsimp [lift, lift_f_zero]
    simp
  ·
    dsimp [lift, lift_f_one]
    simp
  ·
    dsimp
    simp

end ProjectiveResolution

end

namespace ProjectiveResolution

variable [has_zero_object C] [preadditive C] [has_equalizers C] [has_images C]

/--  An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_zero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  exact.lift (f.f 0) (Q.complex.d 1 0) (Q.π.f 0) (congr_funₓ (congr_argₓ HomologicalComplex.Hom.f comm) 0)

/--  An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_one {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 1 ⟶ Q.complex.X 2 :=
  exact.lift (f.f 1 - P.complex.d 1 0 ≫ lift_homotopy_zero_zero f comm) (Q.complex.d 2 1) (Q.complex.d 1 0)
    (by
      simp [lift_homotopy_zero_zero])

/--  An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_succ {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n+1))
    (g' : P.complex.X (n+1) ⟶ Q.complex.X (n+2))
    (w : f.f (n+1) = (P.complex.d (n+1) n ≫ g)+g' ≫ Q.complex.d (n+2) (n+1)) : P.complex.X (n+2) ⟶ Q.complex.X (n+3) :=
  exact.lift (f.f (n+2) - P.complex.d (n+2) (n+1) ≫ g') (Q.complex.d (n+3) (n+2)) (Q.complex.d (n+2) (n+1))
    (by
      simp [w])

/--  Any lift of the zero morphism is homotopic to zero. -/
def lift_homotopy_zero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z} (f : P.complex ⟶ Q.complex)
    (comm : f ≫ Q.π = 0) : Homotopy f 0 := by
  fapply Homotopy.mkInductive
  ·
    exact lift_homotopy_zero_zero f comm
  ·
    simp [lift_homotopy_zero_zero]
  ·
    exact lift_homotopy_zero_one f comm
  ·
    simp [lift_homotopy_zero_one]
  ·
    rintro n ⟨g, g', w⟩
    fconstructor
    ·
      exact lift_homotopy_zero_succ f n g g' w
    ·
      simp [lift_homotopy_zero_succ, w]

/--  Two lifts of the same morphism are homotopic. -/
def lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h := by
  apply homotopy.equiv_sub_zero.inv_fun
  apply lift_homotopy_zero
  simp [g_comm, h_comm]

/--  The lift of the identity morphism is homotopic to the identity chain map. -/
def lift_id_homotopy (X : C) (P : ProjectiveResolution X) : Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) := by
  apply lift_homotopy (𝟙 X) <;> simp

/--  The lift of a composition is homotopic to the composition of the lifts. -/
def lift_comp_homotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (R : ProjectiveResolution Z) : Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply lift_homotopy (f ≫ g) <;> simp

/--  Any two projective resolutions are homotopy equivalent. -/
def HomotopyEquiv {X : C} (P Q : ProjectiveResolution X) : HomotopyEquiv P.complex Q.complex :=
  { Hom := lift (𝟙 X) P Q, inv := lift (𝟙 X) Q P,
    homotopyHomInvId := by
      refine' (lift_comp_homotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _
      simp [category.id_comp]
      apply lift_id_homotopy,
    homotopyInvHomId := by
      refine' (lift_comp_homotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _
      simp [category.id_comp]
      apply lift_id_homotopy }

@[simp, reassoc]
theorem homotopy_equiv_hom_π {X : C} (P Q : ProjectiveResolution X) : (HomotopyEquiv P Q).Hom ≫ Q.π = P.π := by
  simp [HomotopyEquiv]

@[simp, reassoc]
theorem homotopy_equiv_inv_π {X : C} (P Q : ProjectiveResolution X) : (HomotopyEquiv P Q).inv ≫ P.π = Q.π := by
  simp [HomotopyEquiv]

end ProjectiveResolution

section

variable [has_zero_morphisms C] [has_zero_object C] [has_equalizers C] [has_images C]

/--  An arbitrarily chosen projective resolution of an object. -/
abbrev projective_resolution (Z : C) [has_projective_resolution Z] : ChainComplex C ℕ :=
  (has_projective_resolution.out Z).some.complex

/--  The chain map from the arbitrarily chosen projective resolution `projective_resolution Z`
back to the chain complex consisting of `Z` supported in degree `0`. -/
abbrev projective_resolution.π (Z : C) [has_projective_resolution Z] :
    projective_resolution Z ⟶ (ChainComplex.single₀ C).obj Z :=
  (has_projective_resolution.out Z).some.π

/--  The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbrev projective_resolution.lift {X Y : C} (f : X ⟶ Y) [has_projective_resolution X] [has_projective_resolution Y] :
    projective_resolution X ⟶ projective_resolution Y :=
  ProjectiveResolution.lift f _ _

end

variable (C) [preadditive C] [has_zero_object C] [has_equalizers C] [has_images C] [has_projective_resolutions C]

/-- 
Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projective_resolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) :=
  { obj := fun X => (HomotopyCategory.quotient _ _).obj (projective_resolution X),
    map := fun X Y f => (HomotopyCategory.quotient _ _).map (projective_resolution.lift f),
    map_id' := fun X => by
      rw [← (HomotopyCategory.quotient _ _).map_id]
      apply HomotopyCategory.eq_of_homotopy
      apply ProjectiveResolution.lift_id_homotopy,
    map_comp' := fun X Y Z f g => by
      rw [← (HomotopyCategory.quotient _ _).map_comp]
      apply HomotopyCategory.eq_of_homotopy
      apply ProjectiveResolution.lift_comp_homotopy }

end CategoryTheory

