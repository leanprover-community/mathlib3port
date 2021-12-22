import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Project:

- Prove that a functor is additive if it preserves finite biproducts
  (See https://stacks.math.columbia.edu/tag/010M.)
-/


namespace CategoryTheory

/--  A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] (F : C ⥤ D) : Prop where
  map_add' : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f+g) = F.map f+F.map g := by
    run_tac
      obviously

section Preadditive

namespace Functor

section

variable {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] (F : C ⥤ D) [functor.additive F]

@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f+g) = F.map f+F.map g :=
  functor.additive.map_add'

/--  `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps (config := { fullyApplied := ff })]
def map_add_hom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun f g => F.map_add

theorem coe_map_add_hom {X Y : C} : ⇑(F.map_add_hom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y :=
  rfl

@[simp]
theorem map_zero {X Y : C} : F.map (0 : X ⟶ Y) = 0 :=
  F.map_add_hom.map_zero

instance : Additive (𝟭 C) :=
  {  }

instance {E : Type _} [category E] [preadditive E] (G : D ⥤ E) [functor.additive G] : Additive (F ⋙ G) :=
  {  }

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  F.map_add_hom.map_neg _

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  F.map_add_hom.map_sub _ _

theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  F.map_add_hom.map_zsmul _ _

open_locale BigOperators

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
  (Command.declId `map_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`X `Y] [":" `C] "}")
    (Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y))] [] ")")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `F.map
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
        " in "
        `s
        ", "
        (Term.app `f [`a]))])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `F.map [(Term.app `f [`a])])))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [`F.map_add_hom
       [(Term.typeAscription
         ":"
         (Algebra.Group.Hom.«term_→+_» (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) " →+ " (Term.hole "_")))]]
      ")")
     "."
     `map_sum)
    [`f `s])
   [])
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
  (Term.app
   (Term.proj
    (Term.paren
     "("
     [`F.map_add_hom
      [(Term.typeAscription
        ":"
        (Algebra.Group.Hom.«term_→+_» (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) " →+ " (Term.hole "_")))]]
     ")")
    "."
    `map_sum)
   [`f `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.paren
    "("
    [`F.map_add_hom
     [(Term.typeAscription
       ":"
       (Algebra.Group.Hom.«term_→+_» (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) " →+ " (Term.hole "_")))]]
    ")")
   "."
   `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [`F.map_add_hom
    [(Term.typeAscription
      ":"
      (Algebra.Group.Hom.«term_→+_» (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) " →+ " (Term.hole "_")))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Hom.«term_→+_» (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) " →+ " (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Hom.«term_→+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Combinatorics.Quiver.«term_⟶_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 10, (some 10, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Combinatorics.Quiver.«term_⟶_» `X " ⟶ " `Y) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `F.map_add_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `F.map
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `f [`a]))])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    " in "
    `s
    ", "
    (Term.app `F.map [(Term.app `f [`a])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   " in "
   `s
   ", "
   (Term.app `F.map [(Term.app `f [`a])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F.map [(Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  theorem
    map_sum
    { X Y : C } { α : Type _ } ( f : α → X ⟶ Y ) ( s : Finset α ) : F.map ∑ a in s , f a = ∑ a in s , F.map f a
    := ( F.map_add_hom : X ⟶ Y →+ _ ) . map_sum f s

open CategoryTheory.Limits

open_locale ZeroObject

/--  An additive functor takes the zero object to the zero object (up to isomorphism). -/
@[simps]
def map_zero_object [has_zero_object C] [has_zero_object D] : F.obj 0 ≅ 0 :=
  { Hom := 0, inv := 0,
    hom_inv_id' := by
      rw [← F.map_id]
      simp }

end

section InducedCategory

variable {C : Type _} {D : Type _} [category D] [preadditive D] (F : C → D)

instance induced_functor_additive : functor.additive (induced_functor F) :=
  {  }

end InducedCategory

section

noncomputable section

universe v u₁ u₂

variable {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D] [preadditive C] [preadditive D] (F : C ⥤ D)
  [functor.additive F]

open CategoryTheory.Limits

/-- 
An additive functor between preadditive categories creates finite biproducts.
-/
instance map_has_biproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [has_biproduct f] :
    has_biproduct fun j => F.obj (f j) :=
  has_biproduct_of_total
    { x := F.obj (⨁ f), π := fun j => F.map (biproduct.π f j), ι := fun j => F.map (biproduct.ι f j),
      ι_π := fun j j' => by
        simp only [← F.map_comp]
        split_ifs
        ·
          subst h
          simp
        ·
          simp [h] }
    (by
      simp_rw [← F.map_comp, ← F.map_sum, biproduct.total, Functor.map_id])

/-- 
An additive functor between preadditive categories preserves finite biproducts.
-/
@[simps]
def map_biproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [has_biproduct f] :
    F.obj (⨁ f) ≅ ⨁ fun j => F.obj (f j) :=
  { Hom := biproduct.lift fun j => F.map (biproduct.π f j), inv := biproduct.desc fun j => F.map (biproduct.ι f j),
    hom_inv_id' := by
      simp only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum, biproduct.total, F.map_id],
    inv_hom_id' := by
      ext j j'
      simp only [category.comp_id, category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, ← F.map_comp,
        biproduct.ι_π, F.map_dite, dif_ctx_congr, eq_to_hom_map, F.map_zero] }

end

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [category C] [category D] [preadditive C] [preadditive D]

-- failed to format: format: uncaught backtrack exception
instance
  inverse_additive
  ( e : C ≌ D ) [ e.functor.additive ] : e.inverse.additive
  where map_add' X Y f g := by apply e.functor.map_injective simp

end Equivalenceₓ

end Preadditive

end CategoryTheory

