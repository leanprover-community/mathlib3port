import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.Data.Matrix.Dmatrix

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive category
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.

`Mat_ C` has finite biproducts.

## The additive envelope

We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)

As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

## Future work

We should provide a more convenient `Mat R`, when `R` is a ring,
as a category with objects `n : FinType`,
and whose morphisms are matrices with components in `R`.

Ideally this would conveniently interact with both `Mat_` and `matrix`.

-/


open CategoryTheory CategoryTheory.Preadditive

open_locale BigOperators

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [category.{v₁} C] [preadditive C]

/-- 
An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
structure Mat_ : Type max (v₁ + 1) u₁ where
  ι : Type v₁
  [f : Fintype ι]
  [d : DecidableEq ι]
  x : ι → C

attribute [instance] Mat_.F Mat_.D

namespace Mat_

variable {C}

/--  A morphism in `Mat_ C` is a dependently typed matrix of morphisms. -/
@[nolint has_inhabited_instance]
def hom (M N : Mat_ C) : Type v₁ :=
  Dmatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

namespace Hom

/--  The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat_ C) : hom M M := fun i j => if h : i = j then eq_to_hom (congr_argₓ M.X h) else 0

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " Composition of matrices using matrix multiplication. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `comp [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`M `N `K] [":" (Term.app `Mat_ [`C])] "}")
    (Term.explicitBinder "(" [`f] [":" (Term.app `hom [`M `N])] [] ")")
    (Term.explicitBinder "(" [`g] [":" (Term.app `hom [`N `K])] [] ")")]
   [(Term.typeSpec ":" (Term.app `hom [`M `K]))])
  (Command.declValSimple
   ":="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`i `k] [])]
     "=>"
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))))
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
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i `k] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
     ", "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `f [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
/-- Composition of matrices using matrix multiplication. -/
  def comp { M N K : Mat_ C } ( f : hom M N ) ( g : hom N K ) : hom M K := fun i k => ∑ j : N.ι , f i j ≫ g j k

end Hom

section

attribute [local simp] hom.id hom.comp

-- failed to format: format: uncaught backtrack exception
instance
  : category .{ v₁ } ( Mat_ C )
  where
    hom := hom
      id := hom.id
      comp M N K f g := f.comp g
      id_comp' M N f := by simp [ dite_comp ]
      comp_id' M N f := by simp [ comp_dite ]
      assoc'
        M N K L f g h
        :=
        by ext i k simp_rw [ hom.comp , sum_comp , comp_sum , category.assoc ] rw [ Finset.sum_comm ]

theorem id_def (M : Mat_ C) : (𝟙 M : hom M M) = fun i j => if h : i = j then eq_to_hom (congr_argₓ M.X h) else 0 :=
  rfl

theorem id_apply (M : Mat_ C) (i j : M.ι) :
    (𝟙 M : hom M M) i j = if h : i = j then eq_to_hom (congr_argₓ M.X h) else 0 :=
  rfl

@[simp]
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : hom M M) i i = 𝟙 _ := by
  simp [id_apply]

@[simp]
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : hom M M) i j = 0 := by
  simp [id_apply, h]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `comp_def [])
  (Command.declSig
   [(Term.implicitBinder "{" [`M `N `K] [":" (Term.app `Mat_ [`C])] "}")
    (Term.explicitBinder "(" [`f] [":" (Combinatorics.Quiver.«term_⟶_» `M " ⟶ " `N)] [] ")")
    (Term.explicitBinder "(" [`g] [":" (Combinatorics.Quiver.«term_⟶_» `N " ⟶ " `K)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)
     "="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i `k] [])]
       "=>"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
        ", "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))))))))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)
   "="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`i `k] [])]
     "=>"
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i `k] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
     ", "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `f [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem comp_def { M N K : Mat_ C } ( f : M ⟶ N ) ( g : N ⟶ K ) : f ≫ g = fun i k => ∑ j : N.ι , f i j ≫ g j k := rfl

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
  (Command.declId `comp_apply [])
  (Command.declSig
   [(Term.implicitBinder "{" [`M `N `K] [":" (Term.app `Mat_ [`C])] "}")
    (Term.explicitBinder "(" [`f] [":" (Combinatorics.Quiver.«term_⟶_» `M " ⟶ " `N)] [] ")")
    (Term.explicitBinder "(" [`g] [":" (Combinatorics.Quiver.«term_⟶_» `N " ⟶ " `K)] [] ")")
    (Term.simpleBinder [`i `k] [])]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g) [`i `k])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))))))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g) [`i `k])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `N.ι]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `f [`i `j]) " ≫ " (Term.app `g [`j `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `f [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem comp_apply { M N K : Mat_ C } ( f : M ⟶ N ) ( g : N ⟶ K ) i k : f ≫ g i k = ∑ j : N.ι , f i j ≫ g j k := rfl

instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩

end

-- failed to format: format: uncaught backtrack exception
instance
  : preadditive ( Mat_ C )
  where
    homGroup M N := by change AddCommGroupₓ ( Dmatrix M.ι N.ι _ ) infer_instance
      add_comp' M N K f f' g := by ext simp [ Finset.sum_add_distrib ]
      comp_add' M N K f g g' := by ext simp [ Finset.sum_add_distrib ]

@[simp]
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) i j : (f+g) i j = f i j+g i j :=
  rfl

open CategoryTheory.Limits

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nWe now prove that `Mat_ C` has finite biproducts.\n\nBe warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,\nand so the internal indexing of a biproduct may have nothing to do with the external indexing,\neven though the construction we give uses a sigma type.\nSee however `iso_biproduct_embedding`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  []
  [(Command.declId `has_finite_biproducts [])]
  (Command.declSig [] (Term.typeSpec ":" (Term.app `has_finite_biproducts [(Term.app `Mat_ [`C])])))
  (Command.whereStructInst
   "where"
   [(group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `HasBiproductsOfShape
        [(Term.simpleBinder [(Term.simpleBinder [`J `𝒟 `ℱ] [])] [])]
        []
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.exact
              "exact"
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField
                  (Term.structInstLVal `HasBiproduct [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`f] [])]
                    "=>"
                    (Term.app
                     `has_biproduct_of_total
                     [(Term.structInst
                       "{"
                       []
                       [(group
                         (Term.structInstField
                          (Term.structInstLVal `x [])
                          ":="
                          (Term.anonymousCtor
                           "⟨"
                           [(Init.Data.Sigma.Basic.«termΣ_,_»
                             "Σ"
                             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
                             ", "
                             (Term.proj (Term.app `f [`j]) "." `ι))
                            ","
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [(Term.simpleBinder [`p] [])]
                              "=>"
                              (Term.app
                               (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
                               [(Term.proj `p "." (fieldIdx "2"))])))]
                           "⟩"))
                         [","])
                        (group
                         (Term.structInstField
                          (Term.structInstLVal `π [])
                          ":="
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`j `x `y] [])]
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.dsimp
                                  "dsimp"
                                  []
                                  []
                                  []
                                  []
                                  [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))])
                                 [])
                                (group
                                 (Tactic.refine'
                                  "refine'"
                                  (termDepIfThenElse
                                   "if"
                                   `h
                                   ":"
                                   («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                                   "then"
                                   (Term.hole "_")
                                   "else"
                                   (numLit "0")))
                                 [])
                                (group
                                 (Tactic.refine'
                                  "refine'"
                                  (termDepIfThenElse
                                   "if"
                                   `h'
                                   ":"
                                   («term_=_»
                                    (Term.app
                                     (Term.explicit "@" `Eq.ndrec)
                                     [`J
                                      (Term.proj `x "." (fieldIdx "1"))
                                      (Term.fun
                                       "fun"
                                       (Term.basicFun
                                        [(Term.simpleBinder [`j] [])]
                                        "=>"
                                        (Term.proj (Term.app `f [`j]) "." `ι)))
                                      (Term.proj `x "." (fieldIdx "2"))
                                      (Term.hole "_")
                                      `h])
                                    "="
                                    `y)
                                   "then"
                                   (Term.hole "_")
                                   "else"
                                   (numLit "0")))
                                 [])
                                (group (Tactic.apply "apply" `eq_to_hom) [])
                                (group (Tactic.substs "substs" [`h `h']) [])]))))))
                         [","])
                        (group
                         (Term.structInstField
                          (Term.structInstLVal `ι [])
                          ":="
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`j `x `y] [])]
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.dsimp
                                  "dsimp"
                                  []
                                  []
                                  []
                                  []
                                  [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))])
                                 [])
                                (group
                                 (Tactic.refine'
                                  "refine'"
                                  (termDepIfThenElse
                                   "if"
                                   `h
                                   ":"
                                   («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                                   "then"
                                   (Term.hole "_")
                                   "else"
                                   (numLit "0")))
                                 [])
                                (group
                                 (Tactic.refine'
                                  "refine'"
                                  (termDepIfThenElse
                                   "if"
                                   `h'
                                   ":"
                                   («term_=_»
                                    (Term.app
                                     (Term.explicit "@" `Eq.ndrec)
                                     [`J
                                      (Term.proj `y "." (fieldIdx "1"))
                                      (Term.fun
                                       "fun"
                                       (Term.basicFun
                                        [(Term.simpleBinder [`j] [])]
                                        "=>"
                                        (Term.proj (Term.app `f [`j]) "." `ι)))
                                      (Term.proj `y "." (fieldIdx "2"))
                                      (Term.hole "_")
                                      `h])
                                    "="
                                    `x)
                                   "then"
                                   (Term.hole "_")
                                   "else"
                                   (numLit "0")))
                                 [])
                                (group (Tactic.apply "apply" `eq_to_hom) [])
                                (group (Tactic.substs "substs" [`h `h']) [])]))))))
                         [","])
                        (group
                         (Term.structInstField
                          (Term.structInstLVal `ι_π [])
                          ":="
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`j `j'] [])]
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
                                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                                (group
                                 (Tactic.simpRw
                                  "simp_rw"
                                  (Tactic.rwRuleSeq
                                   "["
                                   [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)]
                                   "]")
                                  [])
                                 [])
                                (group
                                 (Tactic.simp
                                  "simp"
                                  []
                                  ["only"]
                                  ["["
                                   [(Tactic.simpLemma [] [] `if_t_t)
                                    ","
                                    (Tactic.simpLemma [] [] `dite_eq_ite)
                                    ","
                                    (Tactic.simpLemma [] [] `dif_ctx_congr)
                                    ","
                                    (Tactic.simpLemma [] [] `limits.comp_zero)
                                    ","
                                    (Tactic.simpLemma [] [] `limits.zero_comp)
                                    ","
                                    (Tactic.simpLemma [] [] `eq_to_hom_trans)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.sum_congr)]
                                   "]"]
                                  [])
                                 [])
                                (group
                                 (Tactic.tacticErw__
                                  "erw"
                                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]")
                                  [])
                                 [])
                                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                                (group
                                 (Tactic.simp
                                  "simp"
                                  []
                                  ["only"]
                                  ["["
                                   [(Tactic.simpLemma [] [] `if_congr)
                                    ","
                                    (Tactic.simpLemma [] [] `if_true)
                                    ","
                                    (Tactic.simpLemma [] [] `dif_ctx_congr)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.mem_univ)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.sum_congr)
                                    ","
                                    (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                                   "]"]
                                  [])
                                 [])
                                (group
                                 (Tactic.splitIfs
                                  "split_ifs"
                                  []
                                  ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]])
                                 [])
                                (group
                                 (Tactic.«tactic·._»
                                  "·"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(group (Tactic.substs "substs" [`h `h']) [])
                                     (group
                                      (Tactic.simp
                                       "simp"
                                       []
                                       ["only"]
                                       ["["
                                        [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                                         ","
                                         (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                                        "]"]
                                       [])
                                      [])])))
                                 [])
                                (group
                                 (Tactic.«tactic·._»
                                  "·"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(group (Tactic.subst "subst" [`h]) [])
                                     (group
                                      (Tactic.simp
                                       "simp"
                                       []
                                       ["only"]
                                       ["["
                                        [(Tactic.simpLemma
                                          []
                                          []
                                          (Term.app
                                           `id_apply_of_ne
                                           [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                                         ","
                                         (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                                        "]"]
                                       [])
                                      [])])))
                                 [])
                                (group
                                 (Tactic.«tactic·._»
                                  "·"
                                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                                 [])]))))))
                         [])]
                       (Term.optEllipsis [])
                       []
                       "}")
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                          (group (tacticFunext__ "funext" [`i₁]) [])
                          (group
                           (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))])
                           [])
                          (group
                           (Tactic.rcases
                            "rcases"
                            [(Tactic.casesTarget [] `i₁)]
                            ["with"
                             (Tactic.rcasesPat.tuple
                              "⟨"
                              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
                              "⟩")])
                           [])
                          (group
                           (Tactic.convert
                            "convert"
                            []
                            (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                            ["using" (numLit "1")])
                           [])
                          (group
                           (Tactic.«tactic·._»
                            "·"
                            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                           [])
                          (group
                           (Tactic.«tactic·._»
                            "·"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group (Tactic.apply "apply" `heq_of_eq) [])
                               (group (Tactic.symm "symm") [])
                               (group (tacticFunext__ "funext" [`i₂]) [])
                               (group
                                (Tactic.rcases
                                 "rcases"
                                 [(Tactic.casesTarget [] `i₂)]
                                 ["with"
                                  (Tactic.rcasesPat.tuple
                                   "⟨"
                                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                                    ","
                                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                                   "⟩")])
                                [])
                               (group
                                (Tactic.simp
                                 "simp"
                                 []
                                 ["only"]
                                 ["["
                                  [(Tactic.simpLemma [] [] `comp_apply)
                                   ","
                                   (Tactic.simpLemma [] [] `dite_comp)
                                   ","
                                   (Tactic.simpLemma [] [] `comp_dite)
                                   ","
                                   (Tactic.simpLemma [] [] `if_t_t)
                                   ","
                                   (Tactic.simpLemma [] [] `dite_eq_ite)
                                   ","
                                   (Tactic.simpLemma [] [] `if_congr)
                                   ","
                                   (Tactic.simpLemma [] [] `if_true)
                                   ","
                                   (Tactic.simpLemma [] [] `dif_ctx_congr)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.mem_univ)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_congr)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.sum_apply)
                                   ","
                                   (Tactic.simpLemma [] [] `limits.comp_zero)
                                   ","
                                   (Tactic.simpLemma [] [] `limits.zero_comp)
                                   ","
                                   (Tactic.simpLemma [] [] `eq_to_hom_trans)
                                   ","
                                   (Tactic.simpLemma [] [] `Mat_.id_apply)]
                                  "]"]
                                 [])
                                [])
                               (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
                               (group
                                (Tactic.«tactic·._»
                                 "·"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group (Tactic.subst "subst" [`h]) [])
                                    (group (Tactic.simp "simp" [] [] [] []) [])])))
                                [])
                               (group
                                (Tactic.«tactic·._»
                                 "·"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                                [])])))
                           [])])))]))))
                 [])]
               (Term.optEllipsis [])
               []
               "}"))
             [])]))))))
     [])])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructField', expected 'Lean.Parser.Command.whereStructField.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.structInst
         "{"
         []
         [(group
           (Term.structInstField
            (Term.structInstLVal `HasBiproduct [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`f] [])]
              "=>"
              (Term.app
               `has_biproduct_of_total
               [(Term.structInst
                 "{"
                 []
                 [(group
                   (Term.structInstField
                    (Term.structInstLVal `x [])
                    ":="
                    (Term.anonymousCtor
                     "⟨"
                     [(Init.Data.Sigma.Basic.«termΣ_,_»
                       "Σ"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
                       ", "
                       (Term.proj (Term.app `f [`j]) "." `ι))
                      ","
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`p] [])]
                        "=>"
                        (Term.app
                         (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
                         [(Term.proj `p "." (fieldIdx "2"))])))]
                     "⟩"))
                   [","])
                  (group
                   (Term.structInstField
                    (Term.structInstLVal `π [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`j `x `y] [])]
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))])
                           [])
                          (group
                           (Tactic.refine'
                            "refine'"
                            (termDepIfThenElse
                             "if"
                             `h
                             ":"
                             («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                             "then"
                             (Term.hole "_")
                             "else"
                             (numLit "0")))
                           [])
                          (group
                           (Tactic.refine'
                            "refine'"
                            (termDepIfThenElse
                             "if"
                             `h'
                             ":"
                             («term_=_»
                              (Term.app
                               (Term.explicit "@" `Eq.ndrec)
                               [`J
                                (Term.proj `x "." (fieldIdx "1"))
                                (Term.fun
                                 "fun"
                                 (Term.basicFun
                                  [(Term.simpleBinder [`j] [])]
                                  "=>"
                                  (Term.proj (Term.app `f [`j]) "." `ι)))
                                (Term.proj `x "." (fieldIdx "2"))
                                (Term.hole "_")
                                `h])
                              "="
                              `y)
                             "then"
                             (Term.hole "_")
                             "else"
                             (numLit "0")))
                           [])
                          (group (Tactic.apply "apply" `eq_to_hom) [])
                          (group (Tactic.substs "substs" [`h `h']) [])]))))))
                   [","])
                  (group
                   (Term.structInstField
                    (Term.structInstLVal `ι [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`j `x `y] [])]
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))])
                           [])
                          (group
                           (Tactic.refine'
                            "refine'"
                            (termDepIfThenElse
                             "if"
                             `h
                             ":"
                             («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                             "then"
                             (Term.hole "_")
                             "else"
                             (numLit "0")))
                           [])
                          (group
                           (Tactic.refine'
                            "refine'"
                            (termDepIfThenElse
                             "if"
                             `h'
                             ":"
                             («term_=_»
                              (Term.app
                               (Term.explicit "@" `Eq.ndrec)
                               [`J
                                (Term.proj `y "." (fieldIdx "1"))
                                (Term.fun
                                 "fun"
                                 (Term.basicFun
                                  [(Term.simpleBinder [`j] [])]
                                  "=>"
                                  (Term.proj (Term.app `f [`j]) "." `ι)))
                                (Term.proj `y "." (fieldIdx "2"))
                                (Term.hole "_")
                                `h])
                              "="
                              `x)
                             "then"
                             (Term.hole "_")
                             "else"
                             (numLit "0")))
                           [])
                          (group (Tactic.apply "apply" `eq_to_hom) [])
                          (group (Tactic.substs "substs" [`h `h']) [])]))))))
                   [","])
                  (group
                   (Term.structInstField
                    (Term.structInstLVal `ι_π [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`j `j'] [])]
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
                          (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                          (group
                           (Tactic.simpRw
                            "simp_rw"
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
                            [])
                           [])
                          (group
                           (Tactic.simp
                            "simp"
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `if_t_t)
                              ","
                              (Tactic.simpLemma [] [] `dite_eq_ite)
                              ","
                              (Tactic.simpLemma [] [] `dif_ctx_congr)
                              ","
                              (Tactic.simpLemma [] [] `limits.comp_zero)
                              ","
                              (Tactic.simpLemma [] [] `limits.zero_comp)
                              ","
                              (Tactic.simpLemma [] [] `eq_to_hom_trans)
                              ","
                              (Tactic.simpLemma [] [] `Finset.sum_congr)]
                             "]"]
                            [])
                           [])
                          (group
                           (Tactic.tacticErw__
                            "erw"
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]")
                            [])
                           [])
                          (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                          (group
                           (Tactic.simp
                            "simp"
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `if_congr)
                              ","
                              (Tactic.simpLemma [] [] `if_true)
                              ","
                              (Tactic.simpLemma [] [] `dif_ctx_congr)
                              ","
                              (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                              ","
                              (Tactic.simpLemma [] [] `Finset.mem_univ)
                              ","
                              (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                              ","
                              (Tactic.simpLemma [] [] `Finset.sum_congr)
                              ","
                              (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                             "]"]
                            [])
                           [])
                          (group
                           (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]])
                           [])
                          (group
                           (Tactic.«tactic·._»
                            "·"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group (Tactic.substs "substs" [`h `h']) [])
                               (group
                                (Tactic.simp
                                 "simp"
                                 []
                                 ["only"]
                                 ["["
                                  [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                                   ","
                                   (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                                  "]"]
                                 [])
                                [])])))
                           [])
                          (group
                           (Tactic.«tactic·._»
                            "·"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group (Tactic.subst "subst" [`h]) [])
                               (group
                                (Tactic.simp
                                 "simp"
                                 []
                                 ["only"]
                                 ["["
                                  [(Tactic.simpLemma
                                    []
                                    []
                                    (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                                   ","
                                   (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                                  "]"]
                                 [])
                                [])])))
                           [])
                          (group
                           (Tactic.«tactic·._»
                            "·"
                            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                           [])]))))))
                   [])]
                 (Term.optEllipsis [])
                 []
                 "}")
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                    (group (tacticFunext__ "funext" [`i₁]) [])
                    (group
                     (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))])
                     [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] `i₁)]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.convert
                      "convert"
                      []
                      (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                      ["using" (numLit "1")])
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.apply "apply" `heq_of_eq) [])
                         (group (Tactic.symm "symm") [])
                         (group (tacticFunext__ "funext" [`i₂]) [])
                         (group
                          (Tactic.rcases
                           "rcases"
                           [(Tactic.casesTarget [] `i₂)]
                           ["with"
                            (Tactic.rcasesPat.tuple
                             "⟨"
                             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                              ","
                              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                             "⟩")])
                          [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `comp_apply)
                             ","
                             (Tactic.simpLemma [] [] `dite_comp)
                             ","
                             (Tactic.simpLemma [] [] `comp_dite)
                             ","
                             (Tactic.simpLemma [] [] `if_t_t)
                             ","
                             (Tactic.simpLemma [] [] `dite_eq_ite)
                             ","
                             (Tactic.simpLemma [] [] `if_congr)
                             ","
                             (Tactic.simpLemma [] [] `if_true)
                             ","
                             (Tactic.simpLemma [] [] `dif_ctx_congr)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                             ","
                             (Tactic.simpLemma [] [] `Finset.mem_univ)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_congr)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                             ","
                             (Tactic.simpLemma [] [] `Finset.sum_apply)
                             ","
                             (Tactic.simpLemma [] [] `limits.comp_zero)
                             ","
                             (Tactic.simpLemma [] [] `limits.zero_comp)
                             ","
                             (Tactic.simpLemma [] [] `eq_to_hom_trans)
                             ","
                             (Tactic.simpLemma [] [] `Mat_.id_apply)]
                            "]"]
                           [])
                          [])
                         (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
                         (group
                          (Tactic.«tactic·._»
                           "·"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
                          [])
                         (group
                          (Tactic.«tactic·._»
                           "·"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                          [])])))
                     [])])))]))))
           [])]
         (Term.optEllipsis [])
         []
         "}"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `HasBiproduct [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`f] [])]
         "=>"
         (Term.app
          `has_biproduct_of_total
          [(Term.structInst
            "{"
            []
            [(group
              (Term.structInstField
               (Term.structInstLVal `x [])
               ":="
               (Term.anonymousCtor
                "⟨"
                [(Init.Data.Sigma.Basic.«termΣ_,_»
                  "Σ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
                  ", "
                  (Term.proj (Term.app `f [`j]) "." `ι))
                 ","
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`p] [])]
                   "=>"
                   (Term.app
                    (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
                    [(Term.proj `p "." (fieldIdx "2"))])))]
                "⟩"))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `π [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`j `x `y] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))])
                      [])
                     (group
                      (Tactic.refine'
                       "refine'"
                       (termDepIfThenElse
                        "if"
                        `h
                        ":"
                        («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                        "then"
                        (Term.hole "_")
                        "else"
                        (numLit "0")))
                      [])
                     (group
                      (Tactic.refine'
                       "refine'"
                       (termDepIfThenElse
                        "if"
                        `h'
                        ":"
                        («term_=_»
                         (Term.app
                          (Term.explicit "@" `Eq.ndrec)
                          [`J
                           (Term.proj `x "." (fieldIdx "1"))
                           (Term.fun
                            "fun"
                            (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                           (Term.proj `x "." (fieldIdx "2"))
                           (Term.hole "_")
                           `h])
                         "="
                         `y)
                        "then"
                        (Term.hole "_")
                        "else"
                        (numLit "0")))
                      [])
                     (group (Tactic.apply "apply" `eq_to_hom) [])
                     (group (Tactic.substs "substs" [`h `h']) [])]))))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `ι [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`j `x `y] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))])
                      [])
                     (group
                      (Tactic.refine'
                       "refine'"
                       (termDepIfThenElse
                        "if"
                        `h
                        ":"
                        («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                        "then"
                        (Term.hole "_")
                        "else"
                        (numLit "0")))
                      [])
                     (group
                      (Tactic.refine'
                       "refine'"
                       (termDepIfThenElse
                        "if"
                        `h'
                        ":"
                        («term_=_»
                         (Term.app
                          (Term.explicit "@" `Eq.ndrec)
                          [`J
                           (Term.proj `y "." (fieldIdx "1"))
                           (Term.fun
                            "fun"
                            (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                           (Term.proj `y "." (fieldIdx "2"))
                           (Term.hole "_")
                           `h])
                         "="
                         `x)
                        "then"
                        (Term.hole "_")
                        "else"
                        (numLit "0")))
                      [])
                     (group (Tactic.apply "apply" `eq_to_hom) [])
                     (group (Tactic.substs "substs" [`h `h']) [])]))))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `ι_π [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`j `j'] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
                     (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                     (group
                      (Tactic.simpRw
                       "simp_rw"
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
                       [])
                      [])
                     (group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `if_t_t)
                         ","
                         (Tactic.simpLemma [] [] `dite_eq_ite)
                         ","
                         (Tactic.simpLemma [] [] `dif_ctx_congr)
                         ","
                         (Tactic.simpLemma [] [] `limits.comp_zero)
                         ","
                         (Tactic.simpLemma [] [] `limits.zero_comp)
                         ","
                         (Tactic.simpLemma [] [] `eq_to_hom_trans)
                         ","
                         (Tactic.simpLemma [] [] `Finset.sum_congr)]
                        "]"]
                       [])
                      [])
                     (group
                      (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") [])
                      [])
                     (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                     (group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `if_congr)
                         ","
                         (Tactic.simpLemma [] [] `if_true)
                         ","
                         (Tactic.simpLemma [] [] `dif_ctx_congr)
                         ","
                         (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                         ","
                         (Tactic.simpLemma [] [] `Finset.mem_univ)
                         ","
                         (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                         ","
                         (Tactic.simpLemma [] [] `Finset.sum_congr)
                         ","
                         (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                        "]"]
                       [])
                      [])
                     (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.substs "substs" [`h `h']) [])
                          (group
                           (Tactic.simp
                            "simp"
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                              ","
                              (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                             "]"]
                            [])
                           [])])))
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.subst "subst" [`h]) [])
                          (group
                           (Tactic.simp
                            "simp"
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma
                               []
                               []
                               (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                              ","
                              (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                             "]"]
                            [])
                           [])])))
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                      [])]))))))
              [])]
            (Term.optEllipsis [])
            []
            "}")
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
               (group (tacticFunext__ "funext" [`i₁]) [])
               (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `i₁)]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
                   "⟩")])
                [])
               (group
                (Tactic.convert
                 "convert"
                 []
                 (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                 ["using" (numLit "1")])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.apply "apply" `heq_of_eq) [])
                    (group (Tactic.symm "symm") [])
                    (group (tacticFunext__ "funext" [`i₂]) [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] `i₂)]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `comp_apply)
                        ","
                        (Tactic.simpLemma [] [] `dite_comp)
                        ","
                        (Tactic.simpLemma [] [] `comp_dite)
                        ","
                        (Tactic.simpLemma [] [] `if_t_t)
                        ","
                        (Tactic.simpLemma [] [] `dite_eq_ite)
                        ","
                        (Tactic.simpLemma [] [] `if_congr)
                        ","
                        (Tactic.simpLemma [] [] `if_true)
                        ","
                        (Tactic.simpLemma [] [] `dif_ctx_congr)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                        ","
                        (Tactic.simpLemma [] [] `Finset.mem_univ)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_congr)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_apply)
                        ","
                        (Tactic.simpLemma [] [] `limits.comp_zero)
                        ","
                        (Tactic.simpLemma [] [] `limits.zero_comp)
                        ","
                        (Tactic.simpLemma [] [] `eq_to_hom_trans)
                        ","
                        (Tactic.simpLemma [] [] `Mat_.id_apply)]
                       "]"]
                      [])
                     [])
                    (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                     [])])))
                [])])))]))))
      [])]
    (Term.optEllipsis [])
    []
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `HasBiproduct [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`f] [])]
        "=>"
        (Term.app
         `has_biproduct_of_total
         [(Term.structInst
           "{"
           []
           [(group
             (Term.structInstField
              (Term.structInstLVal `x [])
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Init.Data.Sigma.Basic.«termΣ_,_»
                 "Σ"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
                 ", "
                 (Term.proj (Term.app `f [`j]) "." `ι))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`p] [])]
                  "=>"
                  (Term.app
                   (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
                   [(Term.proj `p "." (fieldIdx "2"))])))]
               "⟩"))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `π [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`j `x `y] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))])
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (termDepIfThenElse
                       "if"
                       `h
                       ":"
                       («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                       "then"
                       (Term.hole "_")
                       "else"
                       (numLit "0")))
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (termDepIfThenElse
                       "if"
                       `h'
                       ":"
                       («term_=_»
                        (Term.app
                         (Term.explicit "@" `Eq.ndrec)
                         [`J
                          (Term.proj `x "." (fieldIdx "1"))
                          (Term.fun
                           "fun"
                           (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                          (Term.proj `x "." (fieldIdx "2"))
                          (Term.hole "_")
                          `h])
                        "="
                        `y)
                       "then"
                       (Term.hole "_")
                       "else"
                       (numLit "0")))
                     [])
                    (group (Tactic.apply "apply" `eq_to_hom) [])
                    (group (Tactic.substs "substs" [`h `h']) [])]))))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `ι [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`j `x `y] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))])
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (termDepIfThenElse
                       "if"
                       `h
                       ":"
                       («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                       "then"
                       (Term.hole "_")
                       "else"
                       (numLit "0")))
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (termDepIfThenElse
                       "if"
                       `h'
                       ":"
                       («term_=_»
                        (Term.app
                         (Term.explicit "@" `Eq.ndrec)
                         [`J
                          (Term.proj `y "." (fieldIdx "1"))
                          (Term.fun
                           "fun"
                           (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                          (Term.proj `y "." (fieldIdx "2"))
                          (Term.hole "_")
                          `h])
                        "="
                        `x)
                       "then"
                       (Term.hole "_")
                       "else"
                       (numLit "0")))
                     [])
                    (group (Tactic.apply "apply" `eq_to_hom) [])
                    (group (Tactic.substs "substs" [`h `h']) [])]))))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `ι_π [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`j `j'] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
                    (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                    (group
                     (Tactic.simpRw
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
                      [])
                     [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `if_t_t)
                        ","
                        (Tactic.simpLemma [] [] `dite_eq_ite)
                        ","
                        (Tactic.simpLemma [] [] `dif_ctx_congr)
                        ","
                        (Tactic.simpLemma [] [] `limits.comp_zero)
                        ","
                        (Tactic.simpLemma [] [] `limits.zero_comp)
                        ","
                        (Tactic.simpLemma [] [] `eq_to_hom_trans)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_congr)]
                       "]"]
                      [])
                     [])
                    (group
                     (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") [])
                     [])
                    (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `if_congr)
                        ","
                        (Tactic.simpLemma [] [] `if_true)
                        ","
                        (Tactic.simpLemma [] [] `dif_ctx_congr)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                        ","
                        (Tactic.simpLemma [] [] `Finset.mem_univ)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_congr)
                        ","
                        (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                       "]"]
                      [])
                     [])
                    (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.substs "substs" [`h `h']) [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                             ","
                             (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                            "]"]
                           [])
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.subst "subst" [`h]) [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma
                              []
                              []
                              (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                             ","
                             (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                            "]"]
                           [])
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                     [])]))))))
             [])]
           (Term.optEllipsis [])
           []
           "}")
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
              (group (tacticFunext__ "funext" [`i₁]) [])
              (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `i₁)]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.convert
                "convert"
                []
                (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                ["using" (numLit "1")])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.apply "apply" `heq_of_eq) [])
                   (group (Tactic.symm "symm") [])
                   (group (tacticFunext__ "funext" [`i₂]) [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `i₂)]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `comp_apply)
                       ","
                       (Tactic.simpLemma [] [] `dite_comp)
                       ","
                       (Tactic.simpLemma [] [] `comp_dite)
                       ","
                       (Tactic.simpLemma [] [] `if_t_t)
                       ","
                       (Tactic.simpLemma [] [] `dite_eq_ite)
                       ","
                       (Tactic.simpLemma [] [] `if_congr)
                       ","
                       (Tactic.simpLemma [] [] `if_true)
                       ","
                       (Tactic.simpLemma [] [] `dif_ctx_congr)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                       ","
                       (Tactic.simpLemma [] [] `Finset.mem_univ)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_congr)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                       ","
                       (Tactic.simpLemma [] [] `Finset.sum_apply)
                       ","
                       (Tactic.simpLemma [] [] `limits.comp_zero)
                       ","
                       (Tactic.simpLemma [] [] `limits.zero_comp)
                       ","
                       (Tactic.simpLemma [] [] `eq_to_hom_trans)
                       ","
                       (Tactic.simpLemma [] [] `Mat_.id_apply)]
                      "]"]
                     [])
                    [])
                   (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                    [])])))
               [])])))]))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`f] [])]
    "=>"
    (Term.app
     `has_biproduct_of_total
     [(Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `x [])
          ":="
          (Term.anonymousCtor
           "⟨"
           [(Init.Data.Sigma.Basic.«termΣ_,_»
             "Σ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
             ", "
             (Term.proj (Term.app `f [`j]) "." `ι))
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`p] [])]
              "=>"
              (Term.app
               (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
               [(Term.proj `p "." (fieldIdx "2"))])))]
           "⟩"))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `π [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`j `x `y] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))]) [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (termDepIfThenElse
                   "if"
                   `h
                   ":"
                   («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                   "then"
                   (Term.hole "_")
                   "else"
                   (numLit "0")))
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (termDepIfThenElse
                   "if"
                   `h'
                   ":"
                   («term_=_»
                    (Term.app
                     (Term.explicit "@" `Eq.ndrec)
                     [`J
                      (Term.proj `x "." (fieldIdx "1"))
                      (Term.fun
                       "fun"
                       (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                      (Term.proj `x "." (fieldIdx "2"))
                      (Term.hole "_")
                      `h])
                    "="
                    `y)
                   "then"
                   (Term.hole "_")
                   "else"
                   (numLit "0")))
                 [])
                (group (Tactic.apply "apply" `eq_to_hom) [])
                (group (Tactic.substs "substs" [`h `h']) [])]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `ι [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`j `x `y] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))]) [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (termDepIfThenElse
                   "if"
                   `h
                   ":"
                   («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                   "then"
                   (Term.hole "_")
                   "else"
                   (numLit "0")))
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (termDepIfThenElse
                   "if"
                   `h'
                   ":"
                   («term_=_»
                    (Term.app
                     (Term.explicit "@" `Eq.ndrec)
                     [`J
                      (Term.proj `y "." (fieldIdx "1"))
                      (Term.fun
                       "fun"
                       (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                      (Term.proj `y "." (fieldIdx "2"))
                      (Term.hole "_")
                      `h])
                    "="
                    `x)
                   "then"
                   (Term.hole "_")
                   "else"
                   (numLit "0")))
                 [])
                (group (Tactic.apply "apply" `eq_to_hom) [])
                (group (Tactic.substs "substs" [`h `h']) [])]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `ι_π [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`j `j'] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                (group
                 (Tactic.simpRw
                  "simp_rw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
                  [])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `if_t_t)
                    ","
                    (Tactic.simpLemma [] [] `dite_eq_ite)
                    ","
                    (Tactic.simpLemma [] [] `dif_ctx_congr)
                    ","
                    (Tactic.simpLemma [] [] `limits.comp_zero)
                    ","
                    (Tactic.simpLemma [] [] `limits.zero_comp)
                    ","
                    (Tactic.simpLemma [] [] `eq_to_hom_trans)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_congr)]
                   "]"]
                  [])
                 [])
                (group
                 (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") [])
                 [])
                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `if_congr)
                    ","
                    (Tactic.simpLemma [] [] `if_true)
                    ","
                    (Tactic.simpLemma [] [] `dif_ctx_congr)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                    ","
                    (Tactic.simpLemma [] [] `Finset.mem_univ)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_congr)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                   "]"]
                  [])
                 [])
                (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.substs "substs" [`h `h']) [])
                     (group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                         ","
                         (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                        "]"]
                       [])
                      [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.subst "subst" [`h]) [])
                     (group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma
                          []
                          []
                          (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                         ","
                         (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                        "]"]
                       [])
                      [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
                 [])]))))))
         [])]
       (Term.optEllipsis [])
       []
       "}")
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
          (group (tacticFunext__ "funext" [`i₁]) [])
          (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
          (group
           (Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `i₁)]
            ["with"
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
              "⟩")])
           [])
          (group
           (Tactic.convert
            "convert"
            []
            (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            ["using" (numLit "1")])
           [])
          (group
           (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `heq_of_eq) [])
               (group (Tactic.symm "symm") [])
               (group (tacticFunext__ "funext" [`i₂]) [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `i₂)]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                   "⟩")])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `comp_apply)
                   ","
                   (Tactic.simpLemma [] [] `dite_comp)
                   ","
                   (Tactic.simpLemma [] [] `comp_dite)
                   ","
                   (Tactic.simpLemma [] [] `if_t_t)
                   ","
                   (Tactic.simpLemma [] [] `dite_eq_ite)
                   ","
                   (Tactic.simpLemma [] [] `if_congr)
                   ","
                   (Tactic.simpLemma [] [] `if_true)
                   ","
                   (Tactic.simpLemma [] [] `dif_ctx_congr)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                   ","
                   (Tactic.simpLemma [] [] `Finset.mem_univ)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_congr)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_apply)
                   ","
                   (Tactic.simpLemma [] [] `limits.comp_zero)
                   ","
                   (Tactic.simpLemma [] [] `limits.zero_comp)
                   ","
                   (Tactic.simpLemma [] [] `eq_to_hom_trans)
                   ","
                   (Tactic.simpLemma [] [] `Mat_.id_apply)]
                  "]"]
                 [])
                [])
               (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                [])])))
           [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `has_biproduct_of_total
   [(Term.structInst
     "{"
     []
     [(group
       (Term.structInstField
        (Term.structInstLVal `x [])
        ":="
        (Term.anonymousCtor
         "⟨"
         [(Init.Data.Sigma.Basic.«termΣ_,_»
           "Σ"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
           ", "
           (Term.proj (Term.app `f [`j]) "." `ι))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`p] [])]
            "=>"
            (Term.app
             (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
             [(Term.proj `p "." (fieldIdx "2"))])))]
         "⟩"))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `π [])
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j `x `y] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))]) [])
              (group
               (Tactic.refine'
                "refine'"
                (termDepIfThenElse
                 "if"
                 `h
                 ":"
                 («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
                 "then"
                 (Term.hole "_")
                 "else"
                 (numLit "0")))
               [])
              (group
               (Tactic.refine'
                "refine'"
                (termDepIfThenElse
                 "if"
                 `h'
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.explicit "@" `Eq.ndrec)
                   [`J
                    (Term.proj `x "." (fieldIdx "1"))
                    (Term.fun
                     "fun"
                     (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                    (Term.proj `x "." (fieldIdx "2"))
                    (Term.hole "_")
                    `h])
                  "="
                  `y)
                 "then"
                 (Term.hole "_")
                 "else"
                 (numLit "0")))
               [])
              (group (Tactic.apply "apply" `eq_to_hom) [])
              (group (Tactic.substs "substs" [`h `h']) [])]))))))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `ι [])
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j `x `y] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))]) [])
              (group
               (Tactic.refine'
                "refine'"
                (termDepIfThenElse
                 "if"
                 `h
                 ":"
                 («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
                 "then"
                 (Term.hole "_")
                 "else"
                 (numLit "0")))
               [])
              (group
               (Tactic.refine'
                "refine'"
                (termDepIfThenElse
                 "if"
                 `h'
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.explicit "@" `Eq.ndrec)
                   [`J
                    (Term.proj `y "." (fieldIdx "1"))
                    (Term.fun
                     "fun"
                     (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                    (Term.proj `y "." (fieldIdx "2"))
                    (Term.hole "_")
                    `h])
                  "="
                  `x)
                 "then"
                 (Term.hole "_")
                 "else"
                 (numLit "0")))
               [])
              (group (Tactic.apply "apply" `eq_to_hom) [])
              (group (Tactic.substs "substs" [`h `h']) [])]))))))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `ι_π [])
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j `j'] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
              (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
              (group
               (Tactic.simpRw
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
                [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `if_t_t)
                  ","
                  (Tactic.simpLemma [] [] `dite_eq_ite)
                  ","
                  (Tactic.simpLemma [] [] `dif_ctx_congr)
                  ","
                  (Tactic.simpLemma [] [] `limits.comp_zero)
                  ","
                  (Tactic.simpLemma [] [] `limits.zero_comp)
                  ","
                  (Tactic.simpLemma [] [] `eq_to_hom_trans)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_congr)]
                 "]"]
                [])
               [])
              (group (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") []) [])
              (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `if_congr)
                  ","
                  (Tactic.simpLemma [] [] `if_true)
                  ","
                  (Tactic.simpLemma [] [] `dif_ctx_congr)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                  ","
                  (Tactic.simpLemma [] [] `Finset.mem_univ)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_congr)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
                 "]"]
                [])
               [])
              (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.substs "substs" [`h `h']) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                       ","
                       (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                      "]"]
                     [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.subst "subst" [`h]) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma
                        []
                        []
                        (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                       ","
                       (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                      "]"]
                     [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
               [])]))))))
       [])]
     (Term.optEllipsis [])
     []
     "}")
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group (tacticFunext__ "funext" [`i₁]) [])
        (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
        (group
         (Tactic.rcases
          "rcases"
          [(Tactic.casesTarget [] `i₁)]
          ["with"
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
            "⟩")])
         [])
        (group
         (Tactic.convert
          "convert"
          []
          (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          ["using" (numLit "1")])
         [])
        (group
         (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.apply "apply" `heq_of_eq) [])
             (group (Tactic.symm "symm") [])
             (group (tacticFunext__ "funext" [`i₂]) [])
             (group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `i₂)]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `comp_apply)
                 ","
                 (Tactic.simpLemma [] [] `dite_comp)
                 ","
                 (Tactic.simpLemma [] [] `comp_dite)
                 ","
                 (Tactic.simpLemma [] [] `if_t_t)
                 ","
                 (Tactic.simpLemma [] [] `dite_eq_ite)
                 ","
                 (Tactic.simpLemma [] [] `if_congr)
                 ","
                 (Tactic.simpLemma [] [] `if_true)
                 ","
                 (Tactic.simpLemma [] [] `dif_ctx_congr)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                 ","
                 (Tactic.simpLemma [] [] `Finset.mem_univ)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_congr)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
                 ","
                 (Tactic.simpLemma [] [] `Finset.sum_apply)
                 ","
                 (Tactic.simpLemma [] [] `limits.comp_zero)
                 ","
                 (Tactic.simpLemma [] [] `limits.zero_comp)
                 ","
                 (Tactic.simpLemma [] [] `eq_to_hom_trans)
                 ","
                 (Tactic.simpLemma [] [] `Mat_.id_apply)]
                "]"]
               [])
              [])
             (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
              [])])))
         [])])))])
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
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group (tacticFunext__ "funext" [`i₁]) [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `i₁)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        ["using" (numLit "1")])
       [])
      (group
       (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.apply "apply" `heq_of_eq) [])
           (group (Tactic.symm "symm") [])
           (group (tacticFunext__ "funext" [`i₂]) [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `i₂)]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `comp_apply)
               ","
               (Tactic.simpLemma [] [] `dite_comp)
               ","
               (Tactic.simpLemma [] [] `comp_dite)
               ","
               (Tactic.simpLemma [] [] `if_t_t)
               ","
               (Tactic.simpLemma [] [] `dite_eq_ite)
               ","
               (Tactic.simpLemma [] [] `if_congr)
               ","
               (Tactic.simpLemma [] [] `if_true)
               ","
               (Tactic.simpLemma [] [] `dif_ctx_congr)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_univ)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_const_zero)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_congr)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_apply)
               ","
               (Tactic.simpLemma [] [] `limits.comp_zero)
               ","
               (Tactic.simpLemma [] [] `limits.zero_comp)
               ","
               (Tactic.simpLemma [] [] `eq_to_hom_trans)
               ","
               (Tactic.simpLemma [] [] `Mat_.id_apply)]
              "]"]
             [])
            [])
           (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" `heq_of_eq) [])
      (group (Tactic.symm "symm") [])
      (group (tacticFunext__ "funext" [`i₂]) [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `i₂)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `comp_apply)
          ","
          (Tactic.simpLemma [] [] `dite_comp)
          ","
          (Tactic.simpLemma [] [] `comp_dite)
          ","
          (Tactic.simpLemma [] [] `if_t_t)
          ","
          (Tactic.simpLemma [] [] `dite_eq_ite)
          ","
          (Tactic.simpLemma [] [] `if_congr)
          ","
          (Tactic.simpLemma [] [] `if_true)
          ","
          (Tactic.simpLemma [] [] `dif_ctx_congr)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
          ","
          (Tactic.simpLemma [] [] `Finset.mem_univ)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_const_zero)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_congr)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_apply)
          ","
          (Tactic.simpLemma [] [] `limits.comp_zero)
          ","
          (Tactic.simpLemma [] [] `limits.zero_comp)
          ","
          (Tactic.simpLemma [] [] `eq_to_hom_trans)
          ","
          (Tactic.simpLemma [] [] `Mat_.id_apply)]
         "]"]
        [])
       [])
      (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.subst "subst" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.byCases'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `j₁ "=" `j₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `j₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«:»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `comp_apply)
     ","
     (Tactic.simpLemma [] [] `dite_comp)
     ","
     (Tactic.simpLemma [] [] `comp_dite)
     ","
     (Tactic.simpLemma [] [] `if_t_t)
     ","
     (Tactic.simpLemma [] [] `dite_eq_ite)
     ","
     (Tactic.simpLemma [] [] `if_congr)
     ","
     (Tactic.simpLemma [] [] `if_true)
     ","
     (Tactic.simpLemma [] [] `dif_ctx_congr)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
     ","
     (Tactic.simpLemma [] [] `Finset.mem_univ)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_const_zero)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_congr)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_apply)
     ","
     (Tactic.simpLemma [] [] `limits.comp_zero)
     ","
     (Tactic.simpLemma [] [] `limits.zero_comp)
     ","
     (Tactic.simpLemma [] [] `eq_to_hom_trans)
     ","
     (Tactic.simpLemma [] [] `Mat_.id_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Mat_.id_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_to_hom_trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `limits.zero_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `limits.comp_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_dite_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_dite_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_dite_irrel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dif_ctx_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_eq_ite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_t_t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `i₂)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticFunext__ "funext" [`i₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticFunext__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.symm "symm")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.symm', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.apply "apply" `heq_of_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `heq_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert
   "convert"
   []
   (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
   ["using" (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `i₁)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticFunext__ "funext" [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticFunext__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group (tacticFunext__ "funext" [`i₁]) [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`i₁] ["⊢"]))]) [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `i₁)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₁)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₁)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app `Finset.sum_apply [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        ["using" (numLit "1")])
       [])
      (group
       (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.apply "apply" `heq_of_eq) [])
           (group (Tactic.symm "symm") [])
           (group (tacticFunext__ "funext" [`i₂]) [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `i₂)]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j₂)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₂)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `comp_apply)
               ","
               (Tactic.simpLemma [] [] `dite_comp)
               ","
               (Tactic.simpLemma [] [] `comp_dite)
               ","
               (Tactic.simpLemma [] [] `if_t_t)
               ","
               (Tactic.simpLemma [] [] `dite_eq_ite)
               ","
               (Tactic.simpLemma [] [] `if_congr)
               ","
               (Tactic.simpLemma [] [] `if_true)
               ","
               (Tactic.simpLemma [] [] `dif_ctx_congr)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_univ)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_const_zero)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_congr)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_dite_eq)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_apply)
               ","
               (Tactic.simpLemma [] [] `limits.comp_zero)
               ","
               (Tactic.simpLemma [] [] `limits.zero_comp)
               ","
               (Tactic.simpLemma [] [] `eq_to_hom_trans)
               ","
               (Tactic.simpLemma [] [] `Mat_.id_apply)]
              "]"]
             [])
            [])
           (group (Tactic.byCases' "by_cases'" [`h ":"] («term_=_» `j₁ "=" `j₂)) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.subst "subst" [`h]) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
            [])])))
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `x [])
      ":="
      (Term.anonymousCtor
       "⟨"
       [(Init.Data.Sigma.Basic.«termΣ_,_»
         "Σ"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
         ", "
         (Term.proj (Term.app `f [`j]) "." `ι))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`p] [])]
          "=>"
          (Term.app
           (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
           [(Term.proj `p "." (fieldIdx "2"))])))]
       "⟩"))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `π [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j `x `y] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))]) [])
            (group
             (Tactic.refine'
              "refine'"
              (termDepIfThenElse
               "if"
               `h
               ":"
               («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
               "then"
               (Term.hole "_")
               "else"
               (numLit "0")))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (termDepIfThenElse
               "if"
               `h'
               ":"
               («term_=_»
                (Term.app
                 (Term.explicit "@" `Eq.ndrec)
                 [`J
                  (Term.proj `x "." (fieldIdx "1"))
                  (Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                  (Term.proj `x "." (fieldIdx "2"))
                  (Term.hole "_")
                  `h])
                "="
                `y)
               "then"
               (Term.hole "_")
               "else"
               (numLit "0")))
             [])
            (group (Tactic.apply "apply" `eq_to_hom) [])
            (group (Tactic.substs "substs" [`h `h']) [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `ι [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j `x `y] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))]) [])
            (group
             (Tactic.refine'
              "refine'"
              (termDepIfThenElse
               "if"
               `h
               ":"
               («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
               "then"
               (Term.hole "_")
               "else"
               (numLit "0")))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (termDepIfThenElse
               "if"
               `h'
               ":"
               («term_=_»
                (Term.app
                 (Term.explicit "@" `Eq.ndrec)
                 [`J
                  (Term.proj `y "." (fieldIdx "1"))
                  (Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
                  (Term.proj `y "." (fieldIdx "2"))
                  (Term.hole "_")
                  `h])
                "="
                `x)
               "then"
               (Term.hole "_")
               "else"
               (numLit "0")))
             [])
            (group (Tactic.apply "apply" `eq_to_hom) [])
            (group (Tactic.substs "substs" [`h `h']) [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `ι_π [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j `j'] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
            (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simpRw
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `if_t_t)
                ","
                (Tactic.simpLemma [] [] `dite_eq_ite)
                ","
                (Tactic.simpLemma [] [] `dif_ctx_congr)
                ","
                (Tactic.simpLemma [] [] `limits.comp_zero)
                ","
                (Tactic.simpLemma [] [] `limits.zero_comp)
                ","
                (Tactic.simpLemma [] [] `eq_to_hom_trans)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_congr)]
               "]"]
              [])
             [])
            (group (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") []) [])
            (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `if_congr)
                ","
                (Tactic.simpLemma [] [] `if_true)
                ","
                (Tactic.simpLemma [] [] `dif_ctx_congr)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
                ","
                (Tactic.simpLemma [] [] `Finset.mem_univ)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_const_zero)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_congr)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
               "]"]
              [])
             [])
            (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.substs "substs" [`h `h']) [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                     ","
                     (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                    "]"]
                   [])
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.subst "subst" [`h]) [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                     ","
                     (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                    "]"]
                   [])
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
             [])]))))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j `j'] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
        (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group
         (Tactic.simpRw
          "simp_rw"
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
          [])
         [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `if_t_t)
            ","
            (Tactic.simpLemma [] [] `dite_eq_ite)
            ","
            (Tactic.simpLemma [] [] `dif_ctx_congr)
            ","
            (Tactic.simpLemma [] [] `limits.comp_zero)
            ","
            (Tactic.simpLemma [] [] `limits.zero_comp)
            ","
            (Tactic.simpLemma [] [] `eq_to_hom_trans)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_congr)]
           "]"]
          [])
         [])
        (group (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") []) [])
        (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `if_congr)
            ","
            (Tactic.simpLemma [] [] `if_true)
            ","
            (Tactic.simpLemma [] [] `dif_ctx_congr)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
            ","
            (Tactic.simpLemma [] [] `Finset.mem_univ)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_const_zero)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_congr)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
           "]"]
          [])
         [])
        (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.substs "substs" [`h `h']) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
                 ","
                 (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
                "]"]
               [])
              [])])))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.subst "subst" [`h]) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma
                  []
                  []
                  (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
                 ","
                 (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
                "]"]
               [])
              [])])))
         [])
        (group
         (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] []) [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `if_t_t)
          ","
          (Tactic.simpLemma [] [] `dite_eq_ite)
          ","
          (Tactic.simpLemma [] [] `dif_ctx_congr)
          ","
          (Tactic.simpLemma [] [] `limits.comp_zero)
          ","
          (Tactic.simpLemma [] [] `limits.zero_comp)
          ","
          (Tactic.simpLemma [] [] `eq_to_hom_trans)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_congr)]
         "]"]
        [])
       [])
      (group (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") []) [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `if_congr)
          ","
          (Tactic.simpLemma [] [] `if_true)
          ","
          (Tactic.simpLemma [] [] `dif_ctx_congr)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
          ","
          (Tactic.simpLemma [] [] `Finset.mem_univ)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_const_zero)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_congr)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
         "]"]
        [])
       [])
      (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]]) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.substs "substs" [`h `h']) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
               ","
               (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`h]) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
               ","
               (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.subst "subst" [`h]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
          ","
          (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h']))
     ","
     (Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `CategoryTheory.eq_to_hom_refl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `id_apply_of_ne [(Term.hole "_") (Term.hole "_") (Term.hole "_") `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `id_apply_of_ne
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.subst "subst" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.substs "substs" [`h `h']) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
          ","
          (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `CategoryTheory.eq_to_hom_refl)
     ","
     (Tactic.simpLemma [] [] `CategoryTheory.Mat_.id_apply_self)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `CategoryTheory.Mat_.id_apply_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `CategoryTheory.eq_to_hom_refl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.substs "substs" [`h `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.substs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h')]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.splitIfs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `if_congr)
     ","
     (Tactic.simpLemma [] [] `if_true)
     ","
     (Tactic.simpLemma [] [] `dif_ctx_congr)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_dite_irrel)
     ","
     (Tactic.simpLemma [] [] `Finset.mem_univ)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_const_zero)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_congr)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_dite_eq')]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_dite_eq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_dite_irrel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dif_ctx_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_sigma)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_sigma
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `if_t_t)
     ","
     (Tactic.simpLemma [] [] `dite_eq_ite)
     ","
     (Tactic.simpLemma [] [] `dif_ctx_congr)
     ","
     (Tactic.simpLemma [] [] `limits.comp_zero)
     ","
     (Tactic.simpLemma [] [] `limits.zero_comp)
     ","
     (Tactic.simpLemma [] [] `eq_to_hom_trans)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_congr)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_to_hom_trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `limits.zero_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `limits.comp_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dif_ctx_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_eq_ite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_t_t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dite_comp) "," (Tactic.rwRule [] `comp_dite)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x) (Tactic.rcasesPat.one `y)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j `x `y] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))]) [])
        (group
         (Tactic.refine'
          "refine'"
          (termDepIfThenElse
           "if"
           `h
           ":"
           («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
           "then"
           (Term.hole "_")
           "else"
           (numLit "0")))
         [])
        (group
         (Tactic.refine'
          "refine'"
          (termDepIfThenElse
           "if"
           `h'
           ":"
           («term_=_»
            (Term.app
             (Term.explicit "@" `Eq.ndrec)
             [`J
              (Term.proj `y "." (fieldIdx "1"))
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
              (Term.proj `y "." (fieldIdx "2"))
              (Term.hole "_")
              `h])
            "="
            `x)
           "then"
           (Term.hole "_")
           "else"
           (numLit "0")))
         [])
        (group (Tactic.apply "apply" `eq_to_hom) [])
        (group (Tactic.substs "substs" [`h `h']) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))]) [])
      (group
       (Tactic.refine'
        "refine'"
        (termDepIfThenElse
         "if"
         `h
         ":"
         («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
         "then"
         (Term.hole "_")
         "else"
         (numLit "0")))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (termDepIfThenElse
         "if"
         `h'
         ":"
         («term_=_»
          (Term.app
           (Term.explicit "@" `Eq.ndrec)
           [`J
            (Term.proj `y "." (fieldIdx "1"))
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
            (Term.proj `y "." (fieldIdx "2"))
            (Term.hole "_")
            `h])
          "="
          `x)
         "then"
         (Term.hole "_")
         "else"
         (numLit "0")))
       [])
      (group (Tactic.apply "apply" `eq_to_hom) [])
      (group (Tactic.substs "substs" [`h `h']) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.substs "substs" [`h `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.substs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `eq_to_hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_to_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (termDepIfThenElse
    "if"
    `h'
    ":"
    («term_=_»
     (Term.app
      (Term.explicit "@" `Eq.ndrec)
      [`J
       (Term.proj `y "." (fieldIdx "1"))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
       (Term.proj `y "." (fieldIdx "2"))
       (Term.hole "_")
       `h])
     "="
     `x)
    "then"
    (Term.hole "_")
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h'
   ":"
   («term_=_»
    (Term.app
     (Term.explicit "@" `Eq.ndrec)
     [`J
      (Term.proj `y "." (fieldIdx "1"))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
      (Term.proj `y "." (fieldIdx "2"))
      (Term.hole "_")
      `h])
    "="
    `x)
   "then"
   (Term.hole "_")
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    (Term.explicit "@" `Eq.ndrec)
    [`J
     (Term.proj `y "." (fieldIdx "1"))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
     (Term.proj `y "." (fieldIdx "2"))
     (Term.hole "_")
     `h])
   "="
   `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   (Term.explicit "@" `Eq.ndrec)
   [`J
    (Term.proj `y "." (fieldIdx "1"))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
    (Term.proj `y "." (fieldIdx "2"))
    (Term.hole "_")
    `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj `y "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`j]) "." `ι)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`j]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.paren "(" [(Term.app `f [`j]) []] ")") "." `ι)))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `Eq.ndrec)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Eq.ndrec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (termDepIfThenElse
    "if"
    `h
    ":"
    («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
    "then"
    (Term.hole "_")
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h
   ":"
   («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
   "then"
   (Term.hole "_")
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.proj `y "." (fieldIdx "1")) "=" `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj `y "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`y] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j `x `y] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))]) [])
        (group
         (Tactic.refine'
          "refine'"
          (termDepIfThenElse
           "if"
           `h
           ":"
           («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
           "then"
           (Term.hole "_")
           "else"
           (numLit "0")))
         [])
        (group
         (Tactic.refine'
          "refine'"
          (termDepIfThenElse
           "if"
           `h'
           ":"
           («term_=_»
            (Term.app
             (Term.explicit "@" `Eq.ndrec)
             [`J
              (Term.proj `x "." (fieldIdx "1"))
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
              (Term.proj `x "." (fieldIdx "2"))
              (Term.hole "_")
              `h])
            "="
            `y)
           "then"
           (Term.hole "_")
           "else"
           (numLit "0")))
         [])
        (group (Tactic.apply "apply" `eq_to_hom) [])
        (group (Tactic.substs "substs" [`h `h']) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))]) [])
      (group
       (Tactic.refine'
        "refine'"
        (termDepIfThenElse
         "if"
         `h
         ":"
         («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
         "then"
         (Term.hole "_")
         "else"
         (numLit "0")))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (termDepIfThenElse
         "if"
         `h'
         ":"
         («term_=_»
          (Term.app
           (Term.explicit "@" `Eq.ndrec)
           [`J
            (Term.proj `x "." (fieldIdx "1"))
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
            (Term.proj `x "." (fieldIdx "2"))
            (Term.hole "_")
            `h])
          "="
          `y)
         "then"
         (Term.hole "_")
         "else"
         (numLit "0")))
       [])
      (group (Tactic.apply "apply" `eq_to_hom) [])
      (group (Tactic.substs "substs" [`h `h']) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.substs "substs" [`h `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.substs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `eq_to_hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_to_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (termDepIfThenElse
    "if"
    `h'
    ":"
    («term_=_»
     (Term.app
      (Term.explicit "@" `Eq.ndrec)
      [`J
       (Term.proj `x "." (fieldIdx "1"))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
       (Term.proj `x "." (fieldIdx "2"))
       (Term.hole "_")
       `h])
     "="
     `y)
    "then"
    (Term.hole "_")
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h'
   ":"
   («term_=_»
    (Term.app
     (Term.explicit "@" `Eq.ndrec)
     [`J
      (Term.proj `x "." (fieldIdx "1"))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
      (Term.proj `x "." (fieldIdx "2"))
      (Term.hole "_")
      `h])
    "="
    `y)
   "then"
   (Term.hole "_")
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    (Term.explicit "@" `Eq.ndrec)
    [`J
     (Term.proj `x "." (fieldIdx "1"))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
     (Term.proj `x "." (fieldIdx "2"))
     (Term.hole "_")
     `h])
   "="
   `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   (Term.explicit "@" `Eq.ndrec)
   [`J
    (Term.proj `x "." (fieldIdx "1"))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
    (Term.proj `x "." (fieldIdx "2"))
    (Term.hole "_")
    `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.app `f [`j]) "." `ι)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`j]) "." `ι)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`j]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.proj (Term.paren "(" [(Term.app `f [`j]) []] ")") "." `ι)))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `Eq.ndrec)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Eq.ndrec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (termDepIfThenElse
    "if"
    `h
    ":"
    («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
    "then"
    (Term.hole "_")
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h
   ":"
   («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
   "then"
   (Term.hole "_")
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.proj `x "." (fieldIdx "1")) "=" `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`x] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Init.Data.Sigma.Basic.«termΣ_,_»
     "Σ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
     ", "
     (Term.proj (Term.app `f [`j]) "." `ι))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`p] [])]
      "=>"
      (Term.app
       (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
       [(Term.proj `p "." (fieldIdx "2"))])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`p] [])]
    "=>"
    (Term.app
     (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
     [(Term.proj `p "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x) [(Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) "." `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [(Term.proj `p "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [(Term.proj `p "." (fieldIdx "1"))]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
   ", "
   (Term.proj (Term.app `f [`j]) "." `ι))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`j]) "." `ι)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`j]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    We now prove that `Mat_ C` has finite biproducts.
    
    Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
    and so the internal indexing of a biproduct may have nothing to do with the external indexing,
    even though the construction we give uses a sigma type.
    See however `iso_biproduct_embedding`.
    -/
  instance
    has_finite_biproducts
    : has_finite_biproducts Mat_ C
    where
      HasBiproductsOfShape
        J 𝒟 ℱ
        :=
        by
          exact
            {
              HasBiproduct
                :=
                fun
                  f
                    =>
                    has_biproduct_of_total
                      {
                          x := ⟨ Σ j : J , f j . ι , fun p => f p . 1 . x p . 2 ⟩ ,
                            π
                                :=
                                fun
                                  j x y
                                    =>
                                    by
                                      dsimp at x ⊢
                                        refine' if h : x . 1 = j then _ else 0
                                        refine' if h' : @ Eq.ndrec J x . 1 fun j => f j . ι x . 2 _ h = y then _ else 0
                                        apply eq_to_hom
                                        substs h h'
                              ,
                            ι
                                :=
                                fun
                                  j x y
                                    =>
                                    by
                                      dsimp at y ⊢
                                        refine' if h : y . 1 = j then _ else 0
                                        refine' if h' : @ Eq.ndrec J y . 1 fun j => f j . ι y . 2 _ h = x then _ else 0
                                        apply eq_to_hom
                                        substs h h'
                              ,
                            ι_π
                              :=
                              fun
                                j j'
                                  =>
                                  by
                                    ext x y
                                      dsimp
                                      simp_rw [ dite_comp , comp_dite ]
                                      simp
                                        only
                                        [
                                          if_t_t
                                            ,
                                            dite_eq_ite
                                            ,
                                            dif_ctx_congr
                                            ,
                                            limits.comp_zero
                                            ,
                                            limits.zero_comp
                                            ,
                                            eq_to_hom_trans
                                            ,
                                            Finset.sum_congr
                                          ]
                                      erw [ Finset.sum_sigma ]
                                      dsimp
                                      simp
                                        only
                                        [
                                          if_congr
                                            ,
                                            if_true
                                            ,
                                            dif_ctx_congr
                                            ,
                                            Finset.sum_dite_irrel
                                            ,
                                            Finset.mem_univ
                                            ,
                                            Finset.sum_const_zero
                                            ,
                                            Finset.sum_congr
                                            ,
                                            Finset.sum_dite_eq'
                                          ]
                                      split_ifs with h h'
                                      ·
                                        substs h h'
                                          simp
                                            only
                                            [ CategoryTheory.eq_to_hom_refl , CategoryTheory.Mat_.id_apply_self ]
                                      · subst h simp only [ id_apply_of_ne _ _ _ h' , CategoryTheory.eq_to_hom_refl ]
                                      · rfl
                          }
                        by
                          dsimp
                            funext i₁
                            dsimp at i₁ ⊢
                            rcases i₁ with ⟨ j₁ , i₁ ⟩
                            convert Finset.sum_apply _ _ _ using 1
                            · rfl
                            ·
                              apply heq_of_eq
                                symm
                                funext i₂
                                rcases i₂ with ⟨ j₂ , i₂ ⟩
                                simp
                                  only
                                  [
                                    comp_apply
                                      ,
                                      dite_comp
                                      ,
                                      comp_dite
                                      ,
                                      if_t_t
                                      ,
                                      dite_eq_ite
                                      ,
                                      if_congr
                                      ,
                                      if_true
                                      ,
                                      dif_ctx_congr
                                      ,
                                      Finset.sum_dite_irrel
                                      ,
                                      Finset.sum_dite_eq
                                      ,
                                      Finset.mem_univ
                                      ,
                                      Finset.sum_const_zero
                                      ,
                                      Finset.sum_congr
                                      ,
                                      Finset.sum_dite_eq
                                      ,
                                      Finset.sum_apply
                                      ,
                                      limits.comp_zero
                                      ,
                                      limits.zero_comp
                                      ,
                                      eq_to_hom_trans
                                      ,
                                      Mat_.id_apply
                                    ]
                                by_cases' h : j₁ = j₂
                                · subst h simp
                                · simp [ h ]
              }

end Mat_

namespace Functor

variable {C} {D : Type _} [category.{v₁} D] [preadditive D]

attribute [local simp] Mat_.id_apply

/-- 
A functor induces a functor of matrix categories.
-/
@[simps]
def map_Mat_ (F : C ⥤ D) [functor.additive F] : Mat_ C ⥤ Mat_ D :=
  { obj := fun M => ⟨M.ι, fun i => F.obj (M.X i)⟩, map := fun M N f i j => F.map (f i j),
    map_comp' := fun M N K f g => by
      ext i k
      simp }

/-- 
The identity functor induces the identity functor on matrix categories.
-/
@[simps]
def map_Mat_id : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C) :=
  nat_iso.of_components
    (fun M =>
      eq_to_iso
        (by
          cases M
          rfl))
    fun M N f => by
    ext i j
    cases M
    cases N
    simp [comp_dite, dite_comp]

/-- 
Composite functors induce composite functors on matrix categories.
-/
@[simps]
def map_Mat_comp {E : Type _} [category.{v₁} E] [preadditive E] (F : C ⥤ D) [functor.additive F] (G : D ⥤ E)
    [functor.additive G] : (F ⋙ G).mapMat_ ≅ F.map_Mat_ ⋙ G.map_Mat_ :=
  nat_iso.of_components
    (fun M =>
      eq_to_iso
        (by
          cases M
          rfl))
    fun M N f => by
    ext i j
    cases M
    cases N
    simp [comp_dite, dite_comp]

end Functor

namespace Mat_

variable (C)

/--  The embedding of `C` into `Mat_ C` as one-by-one matrices.
(We index the summands by `punit`.) -/
@[simps]
def embedding : C ⥤ Mat_ C :=
  { obj := fun X => ⟨PUnit, fun _ => X⟩, map := fun X Y f => fun _ _ => f,
    map_id' := fun X => by
      ext ⟨⟩ ⟨⟩
      simp ,
    map_comp' := fun X Y Z f g => by
      ext ⟨⟩ ⟨⟩
      simp }

namespace Embedding

-- failed to format: format: uncaught backtrack exception
instance : faithful ( embedding C ) where map_injective' X Y f g h := congr_funₓ ( congr_funₓ h PUnit.unit ) PUnit.unit

-- failed to format: format: uncaught backtrack exception
instance : full ( embedding C ) where Preimage X Y f := f PUnit.unit PUnit.unit

instance : functor.additive (embedding C) :=
  {  }

end Embedding

instance [Inhabited C] : Inhabited (Mat_ C) :=
  ⟨(embedding C).obj (default C)⟩

open CategoryTheory.Limits

variable {C}

/-- 
Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
@[simps]
def iso_biproduct_embedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X i) :=
  { hom := biproduct.lift fun i j k => if h : j = i then eq_to_hom (congr_argₓ M.X h) else 0,
    inv := biproduct.desc fun i j k => if h : i = k then eq_to_hom (congr_argₓ M.X h) else 0,
    hom_inv_id' := by
      simp only [biproduct.lift_desc]
      funext i
      dsimp
      convert Finset.sum_apply _ _ _
      ·
        dsimp
        rfl
      ·
        apply heq_of_eq
        symm
        funext j
        simp only [Finset.sum_apply]
        dsimp
        simp [dite_comp, comp_dite, Mat_.id_apply],
    inv_hom_id' := by
      apply biproduct.hom_ext
      intro i
      apply biproduct.hom_ext'
      intro j
      simp only [category.id_comp, category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, biproduct.ι_π]
      ext ⟨⟩ ⟨⟩
      simp [dite_comp, comp_dite]
      split_ifs
      ·
        subst h
        simp
      ·
        simp [h] }

variable {D : Type u₁} [category.{v₁} D] [preadditive D]

/--  Every `M` is a direct sum of objects from `C`, and `F` preserves biproducts. -/
@[simps]
def additive_obj_iso_biproduct (F : Mat_ C ⥤ D) [functor.additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.map_iso (iso_biproduct_embedding M) ≪≫ F.map_biproduct _

variable [has_finite_biproducts D]

@[reassoc]
theorem additive_obj_iso_biproduct_naturality (F : Mat_ C ⥤ D) [functor.additive F] {M N : Mat_ C} (f : M ⟶ N) :
    F.map f ≫ (additive_obj_iso_biproduct F N).hom =
      (additive_obj_iso_biproduct F M).hom ≫ biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) :=
  by
  ext
  dsimp [embedding]
  simp only [← F.map_comp, biproduct.lift_π, biproduct.matrix_π, category.assoc]
  simp only [← F.map_comp, ← F.map_sum, biproduct.lift_desc, biproduct.lift_π_assoc, comp_sum]
  simp only [comp_def, comp_dite, comp_zero, Finset.sum_dite_eq', Finset.mem_univ, if_true]
  dsimp
  simp only [Finset.sum_singleton, dite_comp, zero_comp]
  congr
  symm
  convert Finset.sum_fn _ _
  simp only [Finset.sum_fn, Finset.sum_dite_eq]
  ext
  simp

@[reassoc]
theorem additive_obj_iso_biproduct_naturality' (F : Mat_ C ⥤ D) [functor.additive F] {M N : Mat_ C} (f : M ⟶ N) :
    (additive_obj_iso_biproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) : _) ≫ (additive_obj_iso_biproduct F N).inv :=
  by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, additive_obj_iso_biproduct_naturality]

/--  Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
def lift (F : C ⥤ D) [functor.additive F] : Mat_ C ⥤ D :=
  { obj := fun X => ⨁ fun i => F.obj (X.X i), map := fun X Y f => biproduct.matrix fun i j => F.map (f i j),
    map_id' := fun X => by
      ext i j
      by_cases' h : i = j
      ·
        subst h
        simp
      ·
        simp [h, Mat_.id_apply],
    map_comp' := fun X Y Z f g => by
      ext i j
      simp }

instance lift_additive (F : C ⥤ D) [functor.additive F] : functor.additive (lift F) :=
  {  }

/--  An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps]
def embedding_lift_iso (F : C ⥤ D) [functor.additive F] : embedding C ⋙ lift F ≅ F :=
  nat_iso.of_components
    (fun X => { hom := biproduct.desc fun P => 𝟙 (F.obj X), inv := biproduct.lift fun P => 𝟙 (F.obj X) }) fun X Y f =>
    by
    dsimp
    ext
    simp only [category.id_comp, biproduct.ι_desc_assoc]
    erw [biproduct.ι_matrix_assoc]
    simp

/-- 
`Mat_.lift F` is the unique additive functor `L : Mat_ C ⥤ D` such that `F ≅ embedding C ⋙ L`.
-/
def lift_unique (F : C ⥤ D) [functor.additive F] (L : Mat_ C ⥤ D) [functor.additive L] (α : embedding C ⋙ L ≅ F) :
    L ≅ lift F :=
  nat_iso.of_components
    (fun M =>
      additive_obj_iso_biproduct L M ≪≫
        (biproduct.map_iso fun i => α.app (M.X i)) ≪≫
          (biproduct.map_iso fun i => (embedding_lift_iso F).symm.app (M.X i)) ≪≫
            (additive_obj_iso_biproduct (lift F) M).symm)
    fun M N f => by
    dsimp only [iso.trans_hom, iso.symm_hom, biproduct.map_iso_hom]
    simp only [additive_obj_iso_biproduct_naturality_assoc]
    simp only [biproduct.matrix_map_assoc, category.assoc]
    simp only [additive_obj_iso_biproduct_naturality']
    simp only [biproduct.map_matrix_assoc, category.assoc]
    congr
    ext j k ⟨⟩
    dsimp
    simp
    convert α.hom.naturality (f j k)
    erw [biproduct.matrix_π]
    simp

/--  Two additive functors `Mat_ C ⥤ D` are naturally isomorphic if
their precompositions with `embedding C` are naturally isomorphic as functors `C ⥤ D`. -/
@[ext]
def ext {F G : Mat_ C ⥤ D} [functor.additive F] [functor.additive G] (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  lift_unique (embedding C ⋙ G) _ α ≪≫ (lift_unique _ _ (iso.refl _)).symm

/-- 
Natural isomorphism needed in the construction of `equivalence_self_of_has_finite_biproducts`.
-/
def equivalence_self_of_has_finite_biproducts_aux [has_finite_biproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  functor.right_unitor _ ≪≫
    (functor.left_unitor _).symm ≪≫ iso_whisker_right (embedding_lift_iso _).symm _ ≪≫ functor.associator _ _ _

/-- 
A preadditive category that already has finite biproducts is equivalent to its additive envelope.

Note that we only prove this for a large category;
otherwise there are universe issues that I haven't attempted to sort out.
-/
def equivalence_self_of_has_finite_biproducts (C : Type (u₁ + 1)) [large_category C] [preadditive C]
    [has_finite_biproducts C] : Mat_ C ≌ C :=
  equivalence.mk (lift (𝟭 C)) (embedding C) (ext equivalence_self_of_has_finite_biproducts_aux)
    (embedding_lift_iso (𝟭 C))

@[simp]
theorem equivalence_self_of_has_finite_biproducts_functor {C : Type (u₁ + 1)} [large_category C] [preadditive C]
    [has_finite_biproducts C] : (equivalence_self_of_has_finite_biproducts C).Functor = lift (𝟭 C) :=
  rfl

@[simp]
theorem equivalence_self_of_has_finite_biproducts_inverse {C : Type (u₁ + 1)} [large_category C] [preadditive C]
    [has_finite_biproducts C] : (equivalence_self_of_has_finite_biproducts C).inverse = embedding C :=
  rfl

end Mat_

end CategoryTheory

