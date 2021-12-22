import Mathbin.Tactic.Abel
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Basic facts about morphisms between biproducts in preadditive categories.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

The remaining lemmas hold in any preadditive category.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.
-/


open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [category.{v} C]

section

variable [has_zero_morphisms.{v} C] [has_binary_biproducts.{v} C]

/-- 
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
theorem is_iso_left_of_is_iso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congr_argₓ (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst) (is_iso.hom_inv_id (biprod.map f g))
        simp only [category.id_comp, category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congr_argₓ (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst) (is_iso.inv_hom_id (biprod.map f g))
        simp only [category.id_comp, category.assoc, biprod.map_fst] at t
        simp only [category.assoc]
        simp [t]⟩⟩⟩

/-- 
If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
theorem is_iso_right_of_is_iso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso g :=
  by
  let this' : is_iso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  exact is_iso_left_of_is_iso_biprod_map g f

end

section

variable [preadditive.{v} C] [has_binary_biproducts.{v} C]

variable {X₁ X₂ Y₁ Y₂ : C}

variable (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/-- 
The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def biprod.of_components : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
  (((biprod.fst ≫
          f₁₁ ≫ biprod.inl)+biprod.fst ≫ f₁₂ ≫ biprod.inr)+biprod.snd ≫ f₂₁ ≫ biprod.inl)+biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
theorem biprod.inl_of_components :
    biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ = (f₁₁ ≫ biprod.inl)+f₁₂ ≫ biprod.inr := by
  simp [biprod.of_components]

@[simp]
theorem biprod.inr_of_components :
    biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ = (f₂₁ ≫ biprod.inl)+f₂₂ ≫ biprod.inr := by
  simp [biprod.of_components]

@[simp]
theorem biprod.of_components_fst :
    biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = (biprod.fst ≫ f₁₁)+biprod.snd ≫ f₂₁ := by
  simp [biprod.of_components]

@[simp]
theorem biprod.of_components_snd :
    biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = (biprod.fst ≫ f₁₂)+biprod.snd ≫ f₂₂ := by
  simp [biprod.of_components]

@[simp]
theorem biprod.of_components_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
    biprod.of_components (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd) (biprod.inr ≫ f ≫ biprod.fst)
        (biprod.inr ≫ f ≫ biprod.snd) =
      f :=
  by
  ext <;> simp

@[simp]
theorem biprod.of_components_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁)
    (f₂₂ : X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) :
    biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
      biprod.of_components ((f₁₁ ≫ g₁₁)+f₁₂ ≫ g₂₁) ((f₁₁ ≫ g₁₂)+f₁₂ ≫ g₂₂) ((f₂₁ ≫ g₁₁)+f₂₂ ≫ g₂₁)
        ((f₂₁ ≫ g₁₂)+f₂₂ ≫ g₂₂) :=
  by
  dsimp [biprod.of_components]
  apply biprod.hom_ext <;>
    apply biprod.hom_ext' <;>
      simp only [add_comp, comp_add, add_comp_assoc, add_zeroₓ, zero_addₓ, biprod.inl_fst, biprod.inl_snd,
        biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc,
        biprod.inr_snd_assoc, comp_zero, zero_comp, category.comp_id, category.assoc]

/-- 
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_upper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
  { hom := biprod.of_components (𝟙 _) r 0 (𝟙 _), inv := biprod.of_components (𝟙 _) (-r) 0 (𝟙 _) }

/-- 
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_lower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
  { hom := biprod.of_components (𝟙 _) 0 r (𝟙 _), inv := biprod.of_components (𝟙 _) 0 (-r) (𝟙 _) }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIf `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,\nthen we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`\nso that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),\nvia Gaussian elimination.\n\n(This is the version of `biprod.gaussian` written in terms of components.)\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `biprod.gaussian' [])
  (Command.optDeclSig
   [(Term.instBinder "[" [] (Term.app `is_iso [`f₁₁]) "]")]
   [(Term.typeSpec
     ":"
     (Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `L)]
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂)
          " ≅ "
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂))
         ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `R)]
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂)
          " ≅ "
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂))
         ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `g₂₂)]
         ":"
         (Combinatorics.Quiver.«term_⟶_» `X₂ " ⟶ " `Y₂)
         ")")])
      ", "
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `L.hom
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
         " ≫ "
         `R.hom))
       "="
       (Term.app `biprod.map [`f₁₁ `g₂₂]))))])
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(Term.app
      `biprod.unipotent_lower
      [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])))])
     ","
     (Term.app
      `biprod.unipotent_upper
      [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂))])
     ","
     («term_-_»
      `f₂₂
      "-"
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       `f₂₁
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂)))
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.ext "ext" [] [])
           "<;>"
           (Tactic.«tactic_<;>_» (Tactic.simp "simp" [] [] [] []) "<;>" (Tactic.abel "abel" [] [])))
          [])])))]
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
     `biprod.unipotent_lower
     [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])))])
    ","
    (Term.app
     `biprod.unipotent_upper
     [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂))])
    ","
    («term_-_»
     `f₂₂
     "-"
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      `f₂₁
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂)))
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.ext "ext" [] [])
          "<;>"
          (Tactic.«tactic_<;>_» (Tactic.simp "simp" [] [] [] []) "<;>" (Tactic.abel "abel" [] [])))
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.ext "ext" [] [])
        "<;>"
        (Tactic.«tactic_<;>_» (Tactic.simp "simp" [] [] [] []) "<;>" (Tactic.abel "abel" [] [])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.ext "ext" [] [])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.simp "simp" [] [] [] []) "<;>" (Tactic.abel "abel" [] [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.simp "simp" [] [] [] []) "<;>" (Tactic.abel "abel" [] []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.abel', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   `f₂₂
   "-"
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `f₂₁
    " ≫ "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `f₂₁
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `inv [`f₁₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₁₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f₂₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `f₂₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biprod.unipotent_upper
   [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `inv [`f₁₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₁₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term-_»
   "-"
   (Term.paren "(" [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `inv [`f₁₁]) " ≫ " `f₁₂) []] ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.unipotent_upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biprod.unipotent_lower
   [(«term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_» "-" (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `inv [`f₁₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₁₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f₂₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term-_»
   "-"
   (Term.paren "(" [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f₂₁ " ≫ " (Term.app `inv [`f₁₁])) []] ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.unipotent_lower
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
    [(Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `L)]
      ":"
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂)
       " ≅ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `R)]
      ":"
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂)
       " ≅ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `g₂₂)]
      ":"
      (Combinatorics.Quiver.«term_⟶_» `X₂ " ⟶ " `Y₂)
      ")")])
   ", "
   («term_=_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `L.hom
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
      " ≫ "
      `R.hom))
    "="
    (Term.app `biprod.map [`f₁₁ `g₂₂])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `L.hom
    " ≫ "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
     " ≫ "
     `R.hom))
   "="
   (Term.app `biprod.map [`f₁₁ `g₂₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `biprod.map [`f₁₁ `g₂₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g₂₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f₁₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `L.hom
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
    " ≫ "
    `R.hom))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
   " ≫ "
   `R.hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R.hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `biprod.of_components [`f₁₁ `f₁₂ `f₂₁ `f₂₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f₂₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f₂₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f₁₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.of_components
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `L.hom
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
/--
    If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
    then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
    so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
    via Gaussian elimination.
    
    (This is the version of `biprod.gaussian` written in terms of components.)
    -/
  def
    biprod.gaussian'
    [ is_iso f₁₁ ]
      :
        Σ'
          ( L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ ) ( R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂ ) ( g₂₂ : X₂ ⟶ Y₂ )
          ,
          L.hom ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ R.hom = biprod.map f₁₁ g₂₂
    :=
      ⟨
        biprod.unipotent_lower - f₂₁ ≫ inv f₁₁
          ,
          biprod.unipotent_upper - inv f₁₁ ≫ f₁₂
          ,
          f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂
          ,
          by ext <;> simp <;> abel
        ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIf `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,\nthen we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`\nso that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),\nvia Gaussian elimination.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `biprod.gaussian [])
  (Command.optDeclSig
   [(Term.explicitBinder
     "("
     [`f]
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂)
       " ⟶ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂))]
     []
     ")")
    (Term.instBinder
     "["
     []
     (Term.app
      `is_iso
      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `biprod.inl
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))])
     "]")]
   [(Term.typeSpec
     ":"
     (Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `L)]
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂)
          " ≅ "
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂))
         ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `R)]
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂)
          " ≅ "
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂))
         ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `g₂₂)]
         ":"
         (Combinatorics.Quiver.«term_⟶_» `X₂ " ⟶ " `Y₂)
         ")")])
      ", "
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `L.hom
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `R.hom))
       "="
       (Term.app
        `biprod.map
        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `biprod.inl
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
         `g₂₂]))))])
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this
           []
           ":="
           (Term.app
            `biprod.gaussian'
            [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              `biprod.inl
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              `biprod.inl
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              `biprod.inr
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              `biprod.inr
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))]))))
        [])
       (group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] [] `biprod.of_components_eq)] "]"] [] []) [])])))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this
          []
          ":="
          (Term.app
           `biprod.gaussian'
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `biprod.inl
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `biprod.inl
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `biprod.inr
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `biprod.inr
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))]))))
       [])
      (group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] [] `biprod.of_components_eq)] "]"] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] [] `biprod.of_components_eq)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.of_components_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `this
     []
     ":="
     (Term.app
      `biprod.gaussian'
      [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `biprod.inl
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `biprod.inl
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `biprod.inr
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `biprod.inr
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biprod.gaussian'
   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `biprod.inl
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `biprod.inl
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `biprod.inr
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `biprod.inr
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inr
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.snd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `biprod.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inr
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inr
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `biprod.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inr
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.snd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `biprod.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.snd))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `biprod.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.gaussian'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `L)]
      ":"
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂)
       " ≅ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `X₁ " ⊞ " `X₂))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `R)]
      ":"
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂)
       " ≅ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_» `Y₁ " ⊞ " `Y₂))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `g₂₂)]
      ":"
      (Combinatorics.Quiver.«term_⟶_» `X₂ " ⟶ " `Y₂)
      ")")])
   ", "
   («term_=_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `L.hom
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `R.hom))
    "="
    (Term.app
     `biprod.map
     [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       `biprod.inl
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
      `g₂₂])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `L.hom
    " ≫ "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `R.hom))
   "="
   (Term.app
    `biprod.map
    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      `biprod.inl
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
     `g₂₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biprod.map
   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `biprod.inl
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
    `g₂₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g₂₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biprod.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `biprod.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `biprod.inl
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.fst))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biprod.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `L.hom
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `R.hom))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `R.hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R.hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `L.hom
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
/--
    If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
    then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
    so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
    via Gaussian elimination.
    -/
  def
    biprod.gaussian
    ( f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ ) [ is_iso biprod.inl ≫ f ≫ biprod.fst ]
      :
        Σ'
          ( L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ ) ( R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂ ) ( g₂₂ : X₂ ⟶ Y₂ )
          ,
          L.hom ≫ f ≫ R.hom = biprod.map biprod.inl ≫ f ≫ biprod.fst g₂₂
    :=
      by
        let
            this
              :=
              biprod.gaussian'
                biprod.inl ≫ f ≫ biprod.fst
                  biprod.inl ≫ f ≫ biprod.snd
                  biprod.inr ≫ f ≫ biprod.fst
                  biprod.inr ≫ f ≫ biprod.snd
          simpa [ biprod.of_components_eq ]

/-- 
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim' [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ := by
  obtain ⟨L, R, g, w⟩ := biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  let this' : is_iso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  let this' : is_iso g := is_iso_right_of_is_iso_biprod_map f₁₁ g
  exact as_iso g

/-- 
If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [is_iso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ := by
  let this' :
    is_iso
      (biprod.of_components (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) :=
    by
    simp only [biprod.of_components_eq]
    infer_instance
  exact
    biprod.iso_elim' (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
      (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)

theorem biprod.column_nonzero_of_iso {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [is_iso f] :
    𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst ≠ 0 ∨ biprod.inl ≫ f ≫ biprod.snd ≠ 0 := by
  by_contra
  rw [not_or_distrib, not_or_distrib, not_not, not_not] at h
  rcases h with ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by
    simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← category.id_comp (inv f), category.assoc, ← biprod.total]
    conv_lhs => slice 2 3rw [comp_add]
    simp only [category.assoc]
    rw [comp_add_assoc, add_comp]
    conv_lhs => congr skip slice 1 3rw [a₂]
    simp only [zero_comp, add_zeroₓ]
    conv_lhs => slice 1 3rw [a₁]
    simp only [zero_comp]
  exact nz (h₁.symm.trans h₀)

end

variable [preadditive.{v} C]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.column_nonzero_of_iso' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`σ `τ] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`σ]) "]")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`τ]) "]")
    (Term.instBinder "[" [] (Term.app `Fintype [`τ]) "]")
    (Term.implicitBinder "{" [`S] [":" (Term.arrow `σ "→" `C)] "}")
    (Term.instBinder "[" [] (Term.app (Term.explicitUniv `has_biproduct ".{" [`v] "}") [`S]) "]")
    (Term.implicitBinder "{" [`T] [":" (Term.arrow `τ "→" `C)] "}")
    (Term.instBinder "[" [] (Term.app (Term.explicitUniv `has_biproduct ".{" [`v] "}") [`T]) "]")
    (Term.explicitBinder "(" [`s] [":" `σ] [] ")")
    (Term.explicitBinder
     "("
     [`f]
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `S)
       " ⟶ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `T))]
     []
     ")")
    (Term.instBinder "[" [] (Term.app `is_iso [`f]) "]")]
   (Term.typeSpec
    ":"
    (Term.arrow
     (Term.forall
      "∀"
      [(Term.simpleBinder [`t] [(Term.typeSpec ":" `τ)])]
      ","
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `biproduct.ι [`S `s])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
       "="
       (numLit "0")))
     "→"
     («term_=_»
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `S [`s])])
      "="
      (numLit "0")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.intro "intro" [`z]) [])
       (group
        (Tactic.set
         "set"
         `x
         []
         ":="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `biproduct.ι [`S `s])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           `f
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `inv [`f])
            " ≫ "
            (Term.app `biproduct.π [`S `s]))))
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₁ []]
           [(Term.typeSpec
             ":"
             («term_=_»
              `x
              "="
              (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `S [`s])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] []) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₀ []]
           [(Term.typeSpec ":" («term_=_» `x "=" (numLit "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] [] []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] (Term.app `category.id_comp [(Term.app `inv [`f])]))
                   ","
                   (Tactic.rwRule [] `category.assoc)
                   ","
                   (Tactic.rwRule ["←"] `biproduct.total)]
                  "]")
                 [])
                [])
               (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_sum_assoc)] "]"] []) [])
               (group
                (Mathlib.Tactic.Conv.convLHS
                 "conv_lhs"
                 []
                 []
                 "=>"
                 (Tactic.Conv.convSeq
                  (Tactic.Conv.convSeq1Indented
                   [(group (Tactic.Conv.congr "congr") [])
                    (group (Tactic.Conv.applyCongr "apply_congr" []) [])
                    (group (Tactic.Conv.convSkip "skip") [])
                    (group
                     (Tactic.Conv.simp
                      "simp"
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`z]))] "]"]
                      [])
                     [])])))
                [])
               (group (Tactic.simp "simp" [] [] [] []) [])]))))))
        [])
       (group (Tactic.exact "exact" (Term.app `h₁.symm.trans [`h₀])) [])])))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`z]) [])
      (group
       (Tactic.set
        "set"
        `x
        []
        ":="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `biproduct.ι [`S `s])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `f
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `inv [`f])
           " ≫ "
           (Term.app `biproduct.π [`S `s]))))
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h₁ []]
          [(Term.typeSpec
            ":"
            («term_=_»
             `x
             "="
             (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `S [`s])])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h₀ []]
          [(Term.typeSpec ":" («term_=_» `x "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] [] []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] (Term.app `category.id_comp [(Term.app `inv [`f])]))
                  ","
                  (Tactic.rwRule [] `category.assoc)
                  ","
                  (Tactic.rwRule ["←"] `biproduct.total)]
                 "]")
                [])
               [])
              (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_sum_assoc)] "]"] []) [])
              (group
               (Mathlib.Tactic.Conv.convLHS
                "conv_lhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(group (Tactic.Conv.congr "congr") [])
                   (group (Tactic.Conv.applyCongr "apply_congr" []) [])
                   (group (Tactic.Conv.convSkip "skip") [])
                   (group
                    (Tactic.Conv.simp
                     "simp"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`z]))] "]"]
                     [])
                    [])])))
               [])
              (group (Tactic.simp "simp" [] [] [] []) [])]))))))
       [])
      (group (Tactic.exact "exact" (Term.app `h₁.symm.trans [`h₀])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `h₁.symm.trans [`h₀]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h₁.symm.trans [`h₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h₁.symm.trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h₀ []]
     [(Term.typeSpec ":" («term_=_» `x "=" (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] [] []) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] (Term.app `category.id_comp [(Term.app `inv [`f])]))
             ","
             (Tactic.rwRule [] `category.assoc)
             ","
             (Tactic.rwRule ["←"] `biproduct.total)]
            "]")
           [])
          [])
         (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_sum_assoc)] "]"] []) [])
         (group
          (Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(group (Tactic.Conv.congr "congr") [])
              (group (Tactic.Conv.applyCongr "apply_congr" []) [])
              (group (Tactic.Conv.convSkip "skip") [])
              (group
               (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`z]))] "]"] [])
               [])])))
          [])
         (group (Tactic.simp "simp" [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `category.id_comp [(Term.app `inv [`f])]))
          ","
          (Tactic.rwRule [] `category.assoc)
          ","
          (Tactic.rwRule ["←"] `biproduct.total)]
         "]")
        [])
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_sum_assoc)] "]"] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.congr "congr") [])
           (group (Tactic.Conv.applyCongr "apply_congr" []) [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group
            (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`z]))] "]"] [])
            [])])))
       [])
      (group (Tactic.simp "simp" [] [] [] []) [])])))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.congr "congr") [])
      (group (Tactic.Conv.applyCongr "apply_congr" []) [])
      (group (Tactic.Conv.convSkip "skip") [])
      (group
       (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`z]))] "]"] [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
theorem
  biproduct.column_nonzero_of_iso'
  { σ τ : Type v }
      [ DecidableEq σ ]
      [ DecidableEq τ ]
      [ Fintype τ ]
      { S : σ → C }
      [ has_biproduct .{ v } S ]
      { T : τ → C }
      [ has_biproduct .{ v } T ]
      ( s : σ )
      ( f : ⨁ S ⟶ ⨁ T )
      [ is_iso f ]
    : ∀ t : τ , biproduct.ι S s ≫ f ≫ biproduct.π T t = 0 → 𝟙 S s = 0
  :=
    by
      intro z
        set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
        have h₁ : x = 𝟙 S s := by simp [ x ]
        have
          h₀
            : x = 0
            :=
            by
              dsimp [ x ]
                rw [ ← category.id_comp inv f , category.assoc , ← biproduct.total ]
                simp only [ comp_sum_assoc ]
                conv_lhs => congr apply_congr skip simp only [ reassoc_of z ]
                simp
        exact h₁.symm.trans h₀

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIf `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,\nthen there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `biproduct.column_nonzero_of_iso [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`σ `τ] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`σ]) "]")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`τ]) "]")
    (Term.instBinder "[" [] (Term.app `Fintype [`τ]) "]")
    (Term.implicitBinder "{" [`S] [":" (Term.arrow `σ "→" `C)] "}")
    (Term.instBinder "[" [] (Term.app (Term.explicitUniv `has_biproduct ".{" [`v] "}") [`S]) "]")
    (Term.implicitBinder "{" [`T] [":" (Term.arrow `τ "→" `C)] "}")
    (Term.instBinder "[" [] (Term.app (Term.explicitUniv `has_biproduct ".{" [`v] "}") [`T]) "]")
    (Term.explicitBinder "(" [`s] [":" `σ] [] ")")
    (Term.explicitBinder
     "("
     [`nz]
     [":"
      («term_≠_»
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.app `S [`s])])
       "≠"
       (numLit "0"))]
     []
     ")")
    (Term.instBinder
     "["
     []
     (Term.forall
      "∀"
      [(Term.simpleBinder [`t] [])]
      ","
      (Term.app `DecidableEq [(Combinatorics.Quiver.«term_⟶_» (Term.app `S [`s]) " ⟶ " (Term.app `T [`t]))]))
     "]")
    (Term.explicitBinder
     "("
     [`f]
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `S)
       " ⟶ "
       (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `T))]
     []
     ")")
    (Term.instBinder "[" [] (Term.app `is_iso [`f]) "]")]
   [(Term.typeSpec
     ":"
     (Term.app
      `Trunc
      [(Init.Data.Sigma.Basic.«termΣ'_,_»
        "Σ'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" `τ]))
        ", "
        («term_≠_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `biproduct.ι [`S `s])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
         "≠"
         (numLit "0")))]))])
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" `truncSigmaOfExists) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`t []]
           []
           ":="
           (Term.app (Term.explicitUniv `biproduct.column_nonzero_of_iso' ".{" [`v] "}") [`s `f]))))
        [])
       (group (byContra "by_contra" [`h]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `not_exists_not)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        [])
       (group (Tactic.exact "exact" (Term.app `nz [(Term.app `t [`h])])) [])])))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" `truncSigmaOfExists) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`t []]
          []
          ":="
          (Term.app (Term.explicitUniv `biproduct.column_nonzero_of_iso' ".{" [`v] "}") [`s `f]))))
       [])
      (group (byContra "by_contra" [`h]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `not_exists_not)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
       [])
      (group (Tactic.exact "exact" (Term.app `nz [(Term.app `t [`h])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `nz [(Term.app `t [`h])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `nz [(Term.app `t [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `t [`h])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `t [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `nz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `not_exists_not)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `not_exists_not
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (byContra "by_contra" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'byContra', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`t []]
     []
     ":="
     (Term.app (Term.explicitUniv `biproduct.column_nonzero_of_iso' ".{" [`v] "}") [`s `f]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.explicitUniv `biproduct.column_nonzero_of_iso' ".{" [`v] "}") [`s `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicitUniv `biproduct.column_nonzero_of_iso' ".{" [`v] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitUniv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `biproduct.column_nonzero_of_iso'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `truncSigmaOfExists)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `truncSigmaOfExists
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Trunc
   [(Init.Data.Sigma.Basic.«termΣ'_,_»
     "Σ'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" `τ]))
     ", "
     («term_≠_»
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `biproduct.ι [`S `s])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
      "≠"
      (numLit "0")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" `τ]))
   ", "
   («term_≠_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `biproduct.ι [`S `s])
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
    "≠"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.ι [`S `s])
    " ≫ "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
   "≠"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `biproduct.ι [`S `s])
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " (Term.app `biproduct.π [`T `t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `biproduct.π [`T `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `biproduct.ι [`S `s])
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
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
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
/--
    If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
    then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
    -/
  def
    biproduct.column_nonzero_of_iso
    { σ τ : Type v }
        [ DecidableEq σ ]
        [ DecidableEq τ ]
        [ Fintype τ ]
        { S : σ → C }
        [ has_biproduct .{ v } S ]
        { T : τ → C }
        [ has_biproduct .{ v } T ]
        ( s : σ )
        ( nz : 𝟙 S s ≠ 0 )
        [ ∀ t , DecidableEq S s ⟶ T t ]
        ( f : ⨁ S ⟶ ⨁ T )
        [ is_iso f ]
      : Trunc Σ' t : τ , biproduct.ι S s ≫ f ≫ biproduct.π T t ≠ 0
    :=
      by
        apply truncSigmaOfExists
          have t := biproduct.column_nonzero_of_iso' .{ v } s f
          by_contra h
          simp only [ not_exists_not ] at h
          exact nz t h

end CategoryTheory

