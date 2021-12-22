import Mathbin.CategoryTheory.Const
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Yoneda
import Mathbin.CategoryTheory.ReflectsIsomorphisms

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

variable {J : Type u₁} [category.{v₁} J]

variable {K : Type u₂} [category.{v₂} K]

variable {C : Type u₃} [category.{v₃} C]

variable {D : Type u₄} [category.{v₄} D]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Functor

variable {J C} (F : J ⥤ C)

/-- 
`F.cones` is the functor assigning to an object `X` the type of
natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
@[simps]
def cones : Cᵒᵖ ⥤ Type max u₁ v₃ :=
  (const J).op ⋙ yoneda.obj F

/-- 
`F.cocones` is the functor assigning to an object `X` the type of
natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
@[simps]
def cocones : C ⥤ Type max u₁ v₃ :=
  const J ⋙ coyoneda.obj (op F)

end Functor

section

variable (J C)

/-- 
Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simps]
def cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type max u₁ v₃ :=
  { obj := functor.cones, map := fun F G f => whisker_left (const J).op (yoneda.map f) }

/-- 
Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simps]
def cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type max u₁ v₃ :=
  { obj := fun F => functor.cocones (unop F), map := fun F G f => whisker_left (const J) (coyoneda.map f) }

end

namespace Limits

/-- 
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟶ F` from the constant `c.X` functor to `F`.

`cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
structure cone (F : J ⥤ C) where
  x : C
  π : (const J).obj X ⟶ F

instance inhabited_cone (F : discrete PUnit ⥤ C) : Inhabited (cone F) :=
  ⟨{ x := F.obj PUnit.unit, π := { app := fun ⟨⟩ => 𝟙 _ } }⟩

@[simp, reassoc]
theorem cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') : c.π.app j ≫ F.map f = c.π.app j' := by
  rw [← c.π.naturality f]
  apply id_comp

/-- 
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure cocone (F : J ⥤ C) where
  x : C
  ι : F ⟶ (const J).obj X

instance inhabited_cocone (F : discrete PUnit ⥤ C) : Inhabited (cocone F) :=
  ⟨{ x := F.obj PUnit.unit, ι := { app := fun ⟨⟩ => 𝟙 _ } }⟩

@[simp, reassoc]
theorem cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') : F.map f ≫ c.ι.app j' = c.ι.app j := by
  rw [c.ι.naturality f]
  apply comp_id

variable {F : J ⥤ C}

namespace Cone

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] []))] "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Equivₓ [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`F] [":" (CategoryTheory.CategoryTheory.Functor.«term_⥤_» `J " ⥤ " `C)] [] ")")]
   [(Term.typeSpec
     ":"
     (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
      (Term.app `cone [`F])
      " ≅ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
       ", "
       (Term.app `F.cones.obj [`X]))))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `Hom [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`c] [])]
         "=>"
         (Term.anonymousCtor "⟨" [(Term.app `op [`c.X]) "," `c.π] "⟩"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `inv [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`c] [])]
         "=>"
         (Term.structInst
          "{"
          []
          [(group
            (Term.structInstField
             (Term.structInstLVal `x [])
             ":="
             (Term.proj (Term.proj `c "." (fieldIdx "1")) "." `unop))
            [","])
           (group (Term.structInstField (Term.structInstLVal `π []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
          (Term.optEllipsis [])
          []
          "}"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `hom_inv_id' [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext1 "ext1" []) [])
           (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
           (group (Tactic.tacticRfl "rfl") [])]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `inv_hom_id' [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext1 "ext1" []) [])
           (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
           (group (Tactic.tacticRfl "rfl") [])]))))
      [])]
    (Term.optEllipsis [])
    []
    "}")
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
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `Hom [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`c] [])]
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `op [`c.X]) "," `c.π] "⟩"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `inv [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`c] [])]
        "=>"
        (Term.structInst
         "{"
         []
         [(group
           (Term.structInstField
            (Term.structInstLVal `x [])
            ":="
            (Term.proj (Term.proj `c "." (fieldIdx "1")) "." `unop))
           [","])
          (group (Term.structInstField (Term.structInstLVal `π []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
         (Term.optEllipsis [])
         []
         "}"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `hom_inv_id' [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.ext1 "ext1" []) [])
          (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
          (group (Tactic.tacticRfl "rfl") [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `inv_hom_id' [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.ext1 "ext1" []) [])
          (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
          (group (Tactic.tacticRfl "rfl") [])]))))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext1 "ext1" []) [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext1 "ext1" []) [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
    [(Term.simpleBinder [`c] [])]
    "=>"
    (Term.structInst
     "{"
     []
     [(group
       (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj (Term.proj `c "." (fieldIdx "1")) "." `unop))
       [","])
      (group (Term.structInstField (Term.structInstLVal `π []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
     (Term.optEllipsis [])
     []
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj (Term.proj `c "." (fieldIdx "1")) "." `unop))
     [","])
    (group (Term.structInstField (Term.structInstLVal `π []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
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
  (Term.proj `c "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `c "." (fieldIdx "1")) "." `unop)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `c "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
   (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.anonymousCtor "⟨" [(Term.app `op [`c.X]) "," `c.π] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.app `op [`c.X]) "," `c.π] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `op [`c.X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `op
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
   (Term.app `cone [`F])
   " ≅ "
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
    ", "
    (Term.app `F.cones.obj [`X])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
   ", "
   (Term.app `F.cones.obj [`X]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F.cones.obj [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.cones.obj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/ @[ simps ]
  def
    Equivₓ
    ( F : J ⥤ C ) : cone F ≅ Σ X , F.cones.obj X
    :=
      {
        Hom := fun c => ⟨ op c.X , c.π ⟩ ,
          inv := fun c => { x := c . 1 . unop , π := c . 2 } ,
          hom_inv_id' := by ext1 cases x rfl ,
          inv_hom_id' := by ext1 cases x rfl
        }

/--  A map to the vertex of a cone naturally induces a cone by composition. -/
@[simps]
def extensions (c : cone F) : yoneda.obj c.X ⋙ ulift_functor.{u₁} ⟶ F.cones :=
  { app := fun X f => (const J).map f.down ≫ c.π }

/--  A map to the vertex of a cone induces a cone by composition. -/
@[simps]
def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
  { x, π := c.extensions.app (op X) ⟨f⟩ }

/--  Whisker a cone by precomposition of a functor. -/
@[simps]
def whisker (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
  { x := c.X, π := whisker_left E c.π }

end Cone

namespace Cocone

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Equivₓ [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`F] [":" (CategoryTheory.CategoryTheory.Functor.«term_⥤_» `J " ⥤ " `C)] [] ")")]
   [(Term.typeSpec
     ":"
     (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
      (Term.app `cocone [`F])
      " ≅ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
       ", "
       (Term.app `F.cocones.obj [`X]))))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `Hom [])
       ":="
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.anonymousCtor "⟨" [`c.X "," `c.ι] "⟩"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `inv [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`c] [])]
         "=>"
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj `c "." (fieldIdx "1"))) [","])
           (group (Term.structInstField (Term.structInstLVal `ι []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
          (Term.optEllipsis [])
          []
          "}"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `hom_inv_id' [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext1 "ext1" []) [])
           (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
           (group (Tactic.tacticRfl "rfl") [])]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `inv_hom_id' [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext1 "ext1" []) [])
           (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
           (group (Tactic.tacticRfl "rfl") [])]))))
      [])]
    (Term.optEllipsis [])
    []
    "}")
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
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `Hom [])
      ":="
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.anonymousCtor "⟨" [`c.X "," `c.ι] "⟩"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `inv [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`c] [])]
        "=>"
        (Term.structInst
         "{"
         []
         [(group (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj `c "." (fieldIdx "1"))) [","])
          (group (Term.structInstField (Term.structInstLVal `ι []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
         (Term.optEllipsis [])
         []
         "}"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `hom_inv_id' [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.ext1 "ext1" []) [])
          (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
          (group (Tactic.tacticRfl "rfl") [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `inv_hom_id' [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.ext1 "ext1" []) [])
          (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
          (group (Tactic.tacticRfl "rfl") [])]))))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext1 "ext1" []) [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext1 "ext1" []) [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] []) [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
    [(Term.simpleBinder [`c] [])]
    "=>"
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj `c "." (fieldIdx "1"))) [","])
      (group (Term.structInstField (Term.structInstLVal `ι []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
     (Term.optEllipsis [])
     []
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group (Term.structInstField (Term.structInstLVal `x []) ":=" (Term.proj `c "." (fieldIdx "1"))) [","])
    (group (Term.structInstField (Term.structInstLVal `ι []) ":=" (Term.proj `c "." (fieldIdx "2"))) [])]
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
  (Term.proj `c "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `c "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.anonymousCtor "⟨" [`c.X "," `c.ι] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`c.X "," `c.ι] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
   (Term.app `cocone [`F])
   " ≅ "
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
    ", "
    (Term.app `F.cocones.obj [`X])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `X)] []))
   ", "
   (Term.app `F.cocones.obj [`X]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F.cocones.obj [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.cocones.obj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
  def
    Equivₓ
    ( F : J ⥤ C ) : cocone F ≅ Σ X , F.cocones.obj X
    :=
      {
        Hom := fun c => ⟨ c.X , c.ι ⟩ ,
          inv := fun c => { x := c . 1 , ι := c . 2 } ,
          hom_inv_id' := by ext1 cases x rfl ,
          inv_hom_id' := by ext1 cases x rfl
        }

/--  A map from the vertex of a cocone naturally induces a cocone by composition. -/
@[simps]
def extensions (c : cocone F) : coyoneda.obj (op c.X) ⋙ ulift_functor.{u₁} ⟶ F.cocones :=
  { app := fun X f => c.ι ≫ (const J).map f.down }

/--  A map from the vertex of a cocone induces a cocone by composition. -/
@[simps]
def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
  { x, ι := c.extensions.app X ⟨f⟩ }

/-- 
Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/
@[simps]
def whisker (E : K ⥤ J) (c : cocone F) : cocone (E ⋙ F) :=
  { x := c.X, ι := whisker_left E c.ι }

end Cocone

/--  A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
@[ext]
structure cone_morphism (A B : cone F) where
  Hom : A.X ⟶ B.X
  w' : ∀ j : J, hom ≫ B.π.app j = A.π.app j := by
    run_tac
      obviously

restate_axiom cone_morphism.w'

attribute [simp, reassoc] cone_morphism.w

instance inhabited_cone_morphism (A : cone F) : Inhabited (cone_morphism A A) :=
  ⟨{ Hom := 𝟙 _ }⟩

-- failed to format: format: uncaught backtrack exception
/-- The category of cones on a given diagram. -/ @[ simps ]
  instance
    cone.category
    : category ( cone F )
    where Hom A B := cone_morphism A B comp X Y Z f g := { Hom := f.hom ≫ g.hom } id B := { Hom := 𝟙 B.X }

namespace Cones

/--  To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
@[ext, simps]
def ext {c c' : cone F} (φ : c.X ≅ c'.X) (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j) : c ≅ c' :=
  { Hom := { Hom := φ.hom }, inv := { Hom := φ.inv, w' := fun j => φ.inv_comp_eq.mpr (w j) } }

/-- 
Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : cone K} (f : c ⟶ d) [i : is_iso f.hom] : is_iso f :=
  ⟨⟨{ Hom := inv f.hom, w' := fun j => (as_iso f.hom).inv_comp_eq.2 (f.w j).symm }, by
      tidy⟩⟩

/-- 
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[simps]
def postcompose {G : J ⥤ C} (α : F ⟶ G) : cone F ⥤ cone G :=
  { obj := fun c => { x := c.X, π := c.π ≫ α }, map := fun c₁ c₂ f => { Hom := f.hom } }

/--  Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
@[simps]
def postcompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) : postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  nat_iso.of_components
    (fun s =>
      cones.ext (iso.refl _)
        (by
          tidy))
    (by
      tidy)

/--  Postcomposing by the identity does not change the cone up to isomorphism. -/
@[simps]
def postcompose_id : postcompose (𝟙 F) ≅ 𝟭 (cone F) :=
  nat_iso.of_components
    (fun s =>
      cones.ext (iso.refl _)
        (by
          tidy))
    (by
      tidy)

/-- 
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[simps]
def postcompose_equivalence {G : J ⥤ C} (α : F ≅ G) : cone F ≌ cone G :=
  { Functor := postcompose α.hom, inverse := postcompose α.inv,
    unitIso :=
      nat_iso.of_components
        (fun s =>
          cones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun s =>
          cones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy) }

/-- 
Whiskering on the left by `E : K ⥤ J` gives a functor from `cone F` to `cone (E ⋙ F)`.
-/
@[simps]
def whiskering (E : K ⥤ J) : cone F ⥤ cone (E ⋙ F) :=
  { obj := fun c => c.whisker E, map := fun c c' f => { Hom := f.hom } }

/-- 
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskering_equivalence (e : K ≌ J) : cone F ≌ cone (e.functor ⋙ F) :=
  { Functor := whiskering e.functor, inverse := whiskering e.inverse ⋙ postcompose (e.inv_fun_id_assoc F).Hom,
    unitIso :=
      nat_iso.of_components
        (fun s =>
          cones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun s =>
          cones.ext (iso.refl _)
            (by
              intro k
              dsimp
              simpa [e.counit_app_functor] using s.w (e.unit_inv.app k)))
        (by
          tidy) }

/-- 
The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[simps Functor inverse unitIso counitIso]
def equivalence_of_reindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : cone F ≌ cone G :=
  (whiskering_equivalence e).trans (postcompose_equivalence α)

section

variable (F)

/--  Forget the cone structure and obtain just the cone point. -/
@[simps]
def forget : cone F ⥤ C :=
  { obj := fun t => t.X, map := fun s t f => f.hom }

variable (G : C ⥤ D)

/--  A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[simps]
def functoriality : cone F ⥤ cone (F ⋙ G) :=
  { obj := fun A =>
      { x := G.obj A.X,
        π :=
          { app := fun j => G.map (A.π.app j),
            naturality' := by
              intros <;> erw [← G.map_comp] <;> tidy } },
    map := fun X Y f =>
      { Hom := G.map f.hom,
        w' := fun j => by
          simp [-cone_morphism.w, ← f.w j] } }

-- failed to format: format: uncaught backtrack exception
instance
  functoriality_full
  [ full G ] [ faithful G ] : full ( functoriality F G )
  where Preimage X Y t := { Hom := G.preimage t.hom , w' := fun j => G.map_injective ( by simpa using t.w j ) }

-- failed to format: format: uncaught backtrack exception
instance
  functoriality_faithful
  [ faithful G ] : faithful ( cones.functoriality F G )
  where map_injective' X Y f g e := by ext1 injection e apply G.map_injective h_1

/-- 
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[simps]
def functoriality_equivalence (e : C ≌ D) : cone F ≌ cone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    functor.associator _ _ _ ≪≫ iso_whisker_left _ e.unit_iso.symm ≪≫ functor.right_unitor _
  { Functor := functoriality F e.functor,
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (postcompose_equivalence f).Functor,
    unitIso :=
      nat_iso.of_components
        (fun c =>
          cones.ext (e.unit_iso.app _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun c =>
          cones.ext (e.counit_iso.app _)
            (by
              tidy))
        (by
          tidy) }

/-- 
If `F` reflects isomorphisms, then `cones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
    reflects_isomorphisms (cones.functoriality K F) := by
  constructor
  intros
  have : is_iso (F.map f.hom) := (cones.forget (K ⋙ F)).map_is_iso ((cones.functoriality K F).map f)
  have := reflects_isomorphisms.reflects F f.hom
  apply cone_iso_of_hom_iso

end

end Cones

/--  A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
@[ext]
structure cocone_morphism (A B : cocone F) where
  Hom : A.X ⟶ B.X
  w' : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j := by
    run_tac
      obviously

instance inhabited_cocone_morphism (A : cocone F) : Inhabited (cocone_morphism A A) :=
  ⟨{ Hom := 𝟙 _ }⟩

restate_axiom cocone_morphism.w'

attribute [simp, reassoc] cocone_morphism.w

-- failed to format: format: uncaught backtrack exception
@[ simps ]
  instance
    cocone.category
    : category ( cocone F )
    where Hom A B := cocone_morphism A B comp _ _ _ f g := { Hom := f.hom ≫ g.hom } id B := { Hom := 𝟙 B.X }

namespace Cocones

/--  To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[ext, simps]
def ext {c c' : cocone F} (φ : c.X ≅ c'.X) (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j) : c ≅ c' :=
  { Hom := { Hom := φ.hom }, inv := { Hom := φ.inv, w' := fun j => φ.comp_inv_eq.mpr (w j).symm } }

/-- 
Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
theorem cocone_iso_of_hom_iso {K : J ⥤ C} {c d : cocone K} (f : c ⟶ d) [i : is_iso f.hom] : is_iso f :=
  ⟨⟨{ Hom := inv f.hom, w' := fun j => (as_iso f.hom).comp_inv_eq.2 (f.w j).symm }, by
      tidy⟩⟩

/--  Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone
for `G`. -/
@[simps]
def precompose {G : J ⥤ C} (α : G ⟶ F) : cocone F ⥤ cocone G :=
  { obj := fun c => { x := c.X, ι := α ≫ c.ι }, map := fun c₁ c₂ f => { Hom := f.hom } }

/--  Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/
def precompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) : precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
  nat_iso.of_components
    (fun s =>
      cocones.ext (iso.refl _)
        (by
          tidy))
    (by
      tidy)

/--  Precomposing by the identity does not change the cocone up to isomorphism. -/
def precompose_id : precompose (𝟙 F) ≅ 𝟭 (cocone F) :=
  nat_iso.of_components
    (fun s =>
      cocones.ext (iso.refl _)
        (by
          tidy))
    (by
      tidy)

/-- 
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/
@[simps]
def precompose_equivalence {G : J ⥤ C} (α : G ≅ F) : cocone F ≌ cocone G :=
  { Functor := precompose α.hom, inverse := precompose α.inv,
    unitIso :=
      nat_iso.of_components
        (fun s =>
          cocones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun s =>
          cocones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy) }

/-- 
Whiskering on the left by `E : K ⥤ J` gives a functor from `cocone F` to `cocone (E ⋙ F)`.
-/
@[simps]
def whiskering (E : K ⥤ J) : cocone F ⥤ cocone (E ⋙ F) :=
  { obj := fun c => c.whisker E, map := fun c c' f => { Hom := f.hom } }

/-- 
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskering_equivalence (e : K ≌ J) : cocone F ≌ cocone (e.functor ⋙ F) :=
  { Functor := whiskering e.functor,
    inverse :=
      whiskering e.inverse ⋙
        precompose ((functor.left_unitor F).inv ≫ whisker_right e.counit_iso.inv F ≫ (functor.associator _ _ _).inv),
    unitIso :=
      nat_iso.of_components
        (fun s =>
          cocones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun s =>
          cocones.ext (iso.refl _)
            (by
              intro k
              dsimp
              simpa [e.counit_inv_app_functor k] using s.w (e.unit.app k)))
        (by
          tidy) }

/-- 
The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[simps functor_obj]
def equivalence_of_reindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : cocone F ≌ cocone G :=
  (whiskering_equivalence e).trans (precompose_equivalence α.symm)

section

variable (F)

/--  Forget the cocone structure and obtain just the cocone point. -/
@[simps]
def forget : cocone F ⥤ C :=
  { obj := fun t => t.X, map := fun s t f => f.hom }

variable (G : C ⥤ D)

/--  A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/
@[simps]
def functoriality : cocone F ⥤ cocone (F ⋙ G) :=
  { obj := fun A =>
      { x := G.obj A.X,
        ι :=
          { app := fun j => G.map (A.ι.app j),
            naturality' := by
              intros <;> erw [← G.map_comp] <;> tidy } },
    map := fun _ _ f =>
      { Hom := G.map f.hom,
        w' := by
          intros <;> rw [← functor.map_comp, cocone_morphism.w] } }

-- failed to format: format: uncaught backtrack exception
instance
  functoriality_full
  [ full G ] [ faithful G ] : full ( functoriality F G )
  where Preimage X Y t := { Hom := G.preimage t.hom , w' := fun j => G.map_injective ( by simpa using t.w j ) }

-- failed to format: format: uncaught backtrack exception
instance
  functoriality_faithful
  [ faithful G ] : faithful ( functoriality F G )
  where map_injective' X Y f g e := by ext1 injection e apply G.map_injective h_1

/-- 
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/
@[simps]
def functoriality_equivalence (e : C ≌ D) : cocone F ≌ cocone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    functor.associator _ _ _ ≪≫ iso_whisker_left _ e.unit_iso.symm ≪≫ functor.right_unitor _
  { Functor := functoriality F e.functor,
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (precompose_equivalence f.symm).Functor,
    unitIso :=
      nat_iso.of_components
        (fun c =>
          cocones.ext (e.unit_iso.app _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun c =>
          cocones.ext (e.counit_iso.app _)
            (by
              intro j
              dsimp
              simp only [← equivalence.counit_inv_app_functor, iso.inv_hom_id_app, map_comp, equivalence.fun_inv_map,
                assoc, id_comp, iso.inv_hom_id_app_assoc]
              dsimp
              simp ))
        fun c c' f => by
        ext
        dsimp
        simp
        dsimp
        simp }

/-- 
If `F` reflects isomorphisms, then `cocones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cocone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
    reflects_isomorphisms (cocones.functoriality K F) := by
  constructor
  intros
  have : is_iso (F.map f.hom) := (cocones.forget (K ⋙ F)).map_is_iso ((cocones.functoriality K F).map f)
  have := reflects_isomorphisms.reflects F f.hom
  apply cocone_iso_of_hom_iso

end

end Cocones

end Limits

namespace Functor

variable {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D)

open CategoryTheory.Limits

/--  The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
@[simps]
def map_cone (c : cone F) : cone (F ⋙ H) :=
  (cones.functoriality F H).obj c

/--  The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/
@[simps]
def map_cocone (c : cocone F) : cocone (F ⋙ H) :=
  (cocones.functoriality F H).obj c

/--  Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially.  -/
def map_cone_morphism {c c' : cone F} (f : c ⟶ c') : H.map_cone c ⟶ H.map_cone c' :=
  (cones.functoriality F H).map f

/--  Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones
functorially. -/
def map_cocone_morphism {c c' : cocone F} (f : c ⟶ c') : H.map_cocone c ⟶ H.map_cocone c' :=
  (cocones.functoriality F H).map f

/--  If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/
def map_cone_inv [is_equivalence H] (c : cone (F ⋙ H)) : cone F :=
  (limits.cones.functoriality_equivalence F (as_equivalence H)).inverse.obj c

/--  `map_cone` is the left inverse to `map_cone_inv`. -/
def map_cone_map_cone_inv {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cone (F ⋙ H)) :
    map_cone H (map_cone_inv H c) ≅ c :=
  (limits.cones.functoriality_equivalence F (as_equivalence H)).counitIso.app c

/--  `map_cone` is the right inverse to `map_cone_inv`. -/
def map_cone_inv_map_cone {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cone F) : map_cone_inv H (map_cone H c) ≅ c :=
  (limits.cones.functoriality_equivalence F (as_equivalence H)).unitIso.symm.app c

/--  If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/
def map_cocone_inv [is_equivalence H] (c : cocone (F ⋙ H)) : cocone F :=
  (limits.cocones.functoriality_equivalence F (as_equivalence H)).inverse.obj c

/--  `map_cocone` is the left inverse to `map_cocone_inv`. -/
def map_cocone_map_cocone_inv {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cocone (F ⋙ H)) :
    map_cocone H (map_cocone_inv H c) ≅ c :=
  (limits.cocones.functoriality_equivalence F (as_equivalence H)).counitIso.app c

/--  `map_cocone` is the right inverse to `map_cocone_inv`. -/
def map_cocone_inv_map_cocone {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cocone F) :
    map_cocone_inv H (map_cocone H c) ≅ c :=
  (limits.cocones.functoriality_equivalence F (as_equivalence H)).unitIso.symm.app c

/--  `functoriality F _ ⋙ postcompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[simps]
def functoriality_comp_postcompose {H H' : C ⥤ D} (α : H ≅ H') :
    cones.functoriality F H ⋙ cones.postcompose (whisker_left F α.hom) ≅ cones.functoriality F H' :=
  nat_iso.of_components
    (fun c =>
      cones.ext (α.app _)
        (by
          tidy))
    (by
      tidy)

/-- 
For `F : J ⥤ C`, given a cone `c : cone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the postcomposition of the cone `H.map_cone` using the isomorphism `α` is
isomorphic to the cone `H'.map_cone`.
-/
@[simps]
def postcompose_whisker_left_map_cone {H H' : C ⥤ D} (α : H ≅ H') (c : cone F) :
    (cones.postcompose (whisker_left F α.hom : _)).obj (H.map_cone c) ≅ H'.map_cone c :=
  (functoriality_comp_postcompose α).app c

/-- 
`map_cone` commutes with `postcompose`. In particular, for `F : J ⥤ C`, given a cone `c : cone F`, a
natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious ways of producing
a cone over `G ⋙ H`, and they are both isomorphic.
-/
@[simps]
def map_cone_postcompose {α : F ⟶ G} {c} :
    H.map_cone ((cones.postcompose α).obj c) ≅ (cones.postcompose (whisker_right α H : _)).obj (H.map_cone c) :=
  cones.ext (iso.refl _)
    (by
      tidy)

/-- 
`map_cone` commutes with `postcompose_equivalence`
-/
@[simps]
def map_cone_postcompose_equivalence_functor {α : F ≅ G} {c} :
    H.map_cone ((cones.postcompose_equivalence α).Functor.obj c) ≅
      (cones.postcompose_equivalence (iso_whisker_right α H : _)).Functor.obj (H.map_cone c) :=
  cones.ext (iso.refl _)
    (by
      tidy)

/--  `functoriality F _ ⋙ precompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[simps]
def functoriality_comp_precompose {H H' : C ⥤ D} (α : H ≅ H') :
    cocones.functoriality F H ⋙ cocones.precompose (whisker_left F α.inv) ≅ cocones.functoriality F H' :=
  nat_iso.of_components
    (fun c =>
      cocones.ext (α.app _)
        (by
          tidy))
    (by
      tidy)

/-- 
For `F : J ⥤ C`, given a cocone `c : cocone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the precomposition of the cocone `H.map_cocone` using the isomorphism `α` is
isomorphic to the cocone `H'.map_cocone`.
-/
@[simps]
def precompose_whisker_left_map_cocone {H H' : C ⥤ D} (α : H ≅ H') (c : cocone F) :
    (cocones.precompose (whisker_left F α.inv : _)).obj (H.map_cocone c) ≅ H'.map_cocone c :=
  (functoriality_comp_precompose α).app c

/-- 
`map_cocone` commutes with `precompose`. In particular, for `F : J ⥤ C`, given a cocone
`c : cocone F`, a natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious
ways of producing a cocone over `G ⋙ H`, and they are both isomorphic.
-/
@[simps]
def map_cocone_precompose {α : F ⟶ G} {c} :
    H.map_cocone ((cocones.precompose α).obj c) ≅ (cocones.precompose (whisker_right α H : _)).obj (H.map_cocone c) :=
  cocones.ext (iso.refl _)
    (by
      tidy)

/-- 
`map_cocone` commutes with `precompose_equivalence`
-/
@[simps]
def map_cocone_precompose_equivalence_functor {α : F ≅ G} {c} :
    H.map_cocone ((cocones.precompose_equivalence α).Functor.obj c) ≅
      (cocones.precompose_equivalence (iso_whisker_right α H : _)).Functor.obj (H.map_cocone c) :=
  cocones.ext (iso.refl _)
    (by
      tidy)

/-- 
`map_cone` commutes with `whisker`
-/
@[simps]
def map_cone_whisker {E : K ⥤ J} {c : cone F} : H.map_cone (c.whisker E) ≅ (H.map_cone c).whisker E :=
  cones.ext (iso.refl _)
    (by
      tidy)

/-- 
`map_cocone` commutes with `whisker`
-/
@[simps]
def map_cocone_whisker {E : K ⥤ J} {c : cocone F} : H.map_cocone (c.whisker E) ≅ (H.map_cocone c).whisker E :=
  cocones.ext (iso.refl _)
    (by
      tidy)

end Functor

end CategoryTheory

namespace CategoryTheory.Limits

section

variable {F : J ⥤ C}

/--  Change a `cocone F` into a `cone F.op`. -/
@[simps]
def cocone.op (c : cocone F) : cone F.op :=
  { x := op c.X,
    π :=
      { app := fun j => (c.ι.app (unop j)).op,
        naturality' := fun j j' f =>
          Quiver.Hom.unop_inj
            (by
              tidy) } }

/--  Change a `cone F` into a `cocone F.op`. -/
@[simps]
def cone.op (c : cone F) : cocone F.op :=
  { x := op c.X,
    ι :=
      { app := fun j => (c.π.app (unop j)).op,
        naturality' := fun j j' f =>
          Quiver.Hom.unop_inj
            (by
              tidy) } }

/--  Change a `cocone F.op` into a `cone F`. -/
@[simps]
def cocone.unop (c : cocone F.op) : cone F :=
  { x := unop c.X,
    π :=
      { app := fun j => (c.ι.app (op j)).unop,
        naturality' := fun j j' f => Quiver.Hom.op_inj (c.ι.naturality f.op).symm } }

/--  Change a `cone F.op` into a `cocone F`. -/
@[simps]
def cone.unop (c : cone F.op) : cocone F :=
  { x := unop c.X,
    ι :=
      { app := fun j => (c.π.app (op j)).unop,
        naturality' := fun j j' f => Quiver.Hom.op_inj (c.π.naturality f.op).symm } }

variable (F)

/-- 
The category of cocones on `F`
is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
@[simps]
def cocone_equivalence_op_cone_op : cocone F ≌ cone F.opᵒᵖ :=
  { Functor :=
      { obj := fun c => op (cocone.op c),
        map := fun X Y f =>
          Quiver.Hom.op
            { Hom := f.hom.op,
              w' := fun j => by
                apply Quiver.Hom.unop_inj
                dsimp
                simp } },
    inverse :=
      { obj := fun c => cone.unop (unop c),
        map := fun X Y f =>
          { Hom := f.unop.hom.unop,
            w' := fun j => by
              apply Quiver.Hom.op_inj
              dsimp
              simp } },
    unitIso :=
      nat_iso.of_components
        (fun c =>
          cocones.ext (iso.refl _)
            (by
              tidy))
        (by
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun c => by
          induction c using Opposite.rec
          dsimp
          apply iso.op
          exact
            cones.ext (iso.refl _)
              (by
                tidy))
        (by
          intros
          have hX : X = op (unop X) := rfl
          revert hX
          generalize unop X = X'
          rintro rfl
          have hY : Y = op (unop Y) := rfl
          revert hY
          generalize unop Y = Y'
          rintro rfl
          apply Quiver.Hom.unop_inj
          apply cone_morphism.ext
          dsimp
          simp ),
    functor_unit_iso_comp' := fun c => by
      apply Quiver.Hom.unop_inj
      ext
      dsimp
      simp }

end

section

variable {F : J ⥤ Cᵒᵖ}

/--  Change a cocone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[simps (config := { rhsMd := semireducible, simpRhs := tt })]
def cone_of_cocone_left_op (c : cocone F.left_op) : cone F :=
  { x := op c.X, π := nat_trans.remove_left_op (c.ι ≫ (const.op_obj_unop (op c.X)).Hom) }

/--  Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps (config := { rhsMd := semireducible, simpRhs := tt })]
def cocone_left_op_of_cone (c : cone F) : cocone F.left_op :=
  { x := unop c.X, ι := nat_trans.left_op c.π }

/--  Change a cone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[simps x]
def cocone_of_cone_left_op (c : cone F.left_op) : cocone F :=
  { x := op c.X, ι := nat_trans.remove_left_op ((const.op_obj_unop (op c.X)).Hom ≫ c.π) }

@[simp]
theorem cocone_of_cone_left_op_ι_app (c : cone F.left_op) j :
    (cocone_of_cone_left_op c).ι.app j = (c.π.app (op j)).op := by
  dsimp [cocone_of_cone_left_op]
  simp

/--  Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps (config := { rhsMd := semireducible, simpRhs := tt })]
def cone_left_op_of_cocone (c : cocone F) : cone F.left_op :=
  { x := unop c.X, π := nat_trans.left_op c.ι }

end

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {F : J ⥤ C}

section

variable (G : C ⥤ D)

/--  The opposite cocone of the image of a cone is the image of the opposite cocone. -/
@[simps (config := { rhsMd := semireducible })]
def map_cone_op (t : cone F) : (G.map_cone t).op ≅ G.op.map_cocone t.op :=
  cocones.ext (iso.refl _)
    (by
      tidy)

/--  The opposite cone of the image of a cocone is the image of the opposite cone. -/
@[simps (config := { rhsMd := semireducible })]
def map_cocone_op {t : cocone F} : (G.map_cocone t).op ≅ G.op.map_cone t.op :=
  cones.ext (iso.refl _)
    (by
      tidy)

end

end CategoryTheory.Functor

