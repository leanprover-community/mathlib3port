/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Bicones
import Mathbin.CategoryTheory.Limits.Comma
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preserves_finite_limits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preserves_finite_limits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `Lan_preserves_finite_limits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_Lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preserves_finite_limits_iff_Lan_preserves_finite_limits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

namespace StructuredArrowCone

open StructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

variable {J : Type w} [SmallCategory J]

variable {K : J ⥤ C} (F : C ⥤ D) (c : Cone K)

/-- Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def toDiagram : J ⥤ StructuredArrow c.x K where
  obj := fun j => StructuredArrow.mk (c.π.app j)
  map := fun j k g =>
    StructuredArrow.homMk g
      (by
        simpa)

/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps]
def diagramToCone {X : D} (G : J ⥤ StructuredArrow X F) : Cone (G ⋙ proj X F ⋙ F) :=
  { x, π := { app := fun j => (G.obj j).Hom } }

/-- Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def toCone {X : D} (f : X ⟶ F.obj c.x) : Cone (toDiagram (F.mapCone c) ⋙ map f ⋙ pre _ K F) where
  x := mk f
  π :=
    { app := fun j => homMk (c.π.app j) rfl,
      naturality' := fun j k g => by
        ext
        dsimp'
        simp }

end StructuredArrowCone

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

/-- A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)

attribute [instance] representably_flat.cofiltered

attribute [local instance] is_cofiltered.nonempty

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[":", expr is_cofiltered_or_empty (structured_arrow X («expr𝟭»() C))]]
instance RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := by
  constructor
  intro X
  haveI : Nonempty (structured_arrow X (𝟭 C)) := ⟨structured_arrow.mk (𝟙 _)⟩
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[\":\", expr is_cofiltered_or_empty (structured_arrow X («expr𝟭»() C))]]"
  · constructor
    
  constructor
  · intro Y Z
    use structured_arrow.mk (𝟙 _)
    use
      structured_arrow.hom_mk Y.hom
        (by
          erw [functor.id_map, category.id_comp])
    use
      structured_arrow.hom_mk Z.hom
        (by
          erw [functor.id_map, category.id_comp])
    
  · intro Y Z f g
    use structured_arrow.mk (𝟙 _)
    use
      structured_arrow.hom_mk Y.hom
        (by
          erw [functor.id_map, category.id_comp])
    ext
    trans Z.hom <;> simp
    

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[":", expr is_cofiltered_or_empty (structured_arrow X «expr ⋙ »(F, G))]]
instance RepresentablyFlat.comp (F : C ⥤ D) (G : D ⥤ E) [RepresentablyFlat F] [RepresentablyFlat G] :
    RepresentablyFlat (F ⋙ G) := by
  constructor
  intro X
  have : Nonempty (structured_arrow X (F ⋙ G)) := by
    have f₁ : structured_arrow X G := Nonempty.some inferInstance
    have f₂ : structured_arrow f₁.right F := Nonempty.some inferInstance
    exact ⟨structured_arrow.mk (f₁.hom ≫ G.map f₂.hom)⟩
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[\":\", expr is_cofiltered_or_empty (structured_arrow X «expr ⋙ »(F, G))]]"
  · constructor
    
  constructor
  · intro Y Z
    let W := @is_cofiltered.min (structured_arrow X G) _ _ (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom)
    let Y' : W ⟶ _ := is_cofiltered.min_to_left _ _
    let Z' : W ⟶ _ := is_cofiltered.min_to_right _ _
    let W' :=
      @is_cofiltered.min (structured_arrow W.right F) _ _ (structured_arrow.mk Y'.right) (structured_arrow.mk Z'.right)
    let Y'' : W' ⟶ _ := is_cofiltered.min_to_left _ _
    let Z'' : W' ⟶ _ := is_cofiltered.min_to_right _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use
      structured_arrow.hom_mk Y''.right
        (by
          simp [← G.map_comp])
    use
      structured_arrow.hom_mk Z''.right
        (by
          simp [← G.map_comp])
    
  · intro Y Z f g
    let W :=
      @is_cofiltered.eq (structured_arrow X G) _ _ (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom)
        (structured_arrow.hom_mk (F.map f.right) (structured_arrow.w f))
        (structured_arrow.hom_mk (F.map g.right) (structured_arrow.w g))
    let h : W ⟶ _ := is_cofiltered.eq_hom _ _
    let h_cond : h ≫ _ = h ≫ _ := is_cofiltered.eq_condition _ _
    let W' :=
      @is_cofiltered.eq (structured_arrow W.right F) _ _ (structured_arrow.mk h.right)
        (structured_arrow.mk (h.right ≫ F.map f.right)) (structured_arrow.hom_mk f.right rfl)
        (structured_arrow.hom_mk g.right (congr_arg comma_morphism.right h_cond).symm)
    let h' : W' ⟶ _ := is_cofiltered.eq_hom _ _
    let h'_cond : h' ≫ _ = h' ≫ _ := is_cofiltered.eq_condition _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use
      structured_arrow.hom_mk h'.right
        (by
          simp [← G.map_comp])
    ext
    exact (congr_arg comma_morphism.right h'_cond : _)
    

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

attribute [local instance] has_finite_limits_of_has_finite_limits_of_size

instance (priority := 100) cofiltered_of_has_finite_limits [HasFiniteLimits C] : IsCofiltered C where
  cocone_objs := fun A B => ⟨Limits.prod A B, Limits.prod.fst, Limits.prod.snd, trivialₓ⟩
  cocone_maps := fun A B f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩
  Nonempty := ⟨⊤_ C⟩

theorem flat_of_preserves_finite_limits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X => by
    haveI : has_finite_limits (structured_arrow X F) := by
      apply has_finite_limits_of_has_finite_limits_of_size.{v₁} (structured_arrow X F)
      intro J sJ fJ
      skip
      constructor
    infer_instance⟩

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

open StructuredArrowCone

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}

variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

include hc

/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.x ⟶ F.obj c.x :=
  let s' := IsCofiltered.cone (toDiagram s ⋙ StructuredArrow.pre _ K F)
  s'.x.Hom ≫
    (F.map <|
      hc.lift <|
        (Cones.postcompose
              ({ app := fun X => 𝟙 _,
                naturality' := by
                  simp } :
                (toDiagram s ⋙ pre s.x K F) ⋙ proj s.x F ⟶ K)).obj <|
          (StructuredArrow.proj s.x F).mapCone s')

theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simpa [lift, ← functor.map_comp]

attribute [local simp] eq_to_hom_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
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
              `α₁
              []
              [(Term.typeSpec
                ":"
                (Combinatorics.Quiver.Basic.«term_⟶_»
                 (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                  (Term.app `to_diagram [(Term.app `F.map_cone [`c])])
                  " ⋙ "
                  (Term.app `map [`f₁]))
                 " ⟶ "
                 (Term.app `to_diagram [`s])))]
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
                   [`X]
                   []
                   "=>"
                   (Term.app
                    `eq_to_hom
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] ["←"] `h₁)] "]"] [])
                          [])])))]))))
                ","
                (Term.structInstField
                 (Term.structInstLVal `naturality' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                       (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))]
               (Term.optEllipsis [])
               []
               "}"))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `α₂
              []
              [(Term.typeSpec
                ":"
                (Combinatorics.Quiver.Basic.«term_⟶_»
                 (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                  (Term.app `to_diagram [(Term.app `F.map_cone [`c])])
                  " ⋙ "
                  (Term.app `map [`f₂]))
                 " ⟶ "
                 (Term.app `to_diagram [`s])))]
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
                   [`X]
                   []
                   "=>"
                   (Term.app
                    `eq_to_hom
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] ["←"] `h₂)] "]"] [])
                          [])])))]))))
                ","
                (Term.structInstField
                 (Term.structInstLVal `naturality' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                       (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))]
               (Term.optEllipsis [])
               []
               "}"))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c₁
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `cone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   (Term.app `to_diagram [`s])
                   " ⋙ "
                   (Term.app `pre [`s.X `K `F]))]))]
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `cones.postcompose
                 [(Term.paren
                   "("
                   [(Term.app `whisker_right [`α₁ (Term.app `pre [`s.X `K `F])])
                    [(Term.typeAscription ":" (Term.hole "_"))]]
                   ")")])
                "."
                `obj)
               [(Term.app `to_cone [`F `c `f₁])]))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c₂
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `cone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   (Term.app `to_diagram [`s])
                   " ⋙ "
                   (Term.app `pre [`s.X `K `F]))]))]
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `cones.postcompose
                 [(Term.paren
                   "("
                   [(Term.app `whisker_right [`α₂ (Term.app `pre [`s.X `K `F])])
                    [(Term.typeAscription ":" (Term.hole "_"))]]
                   ")")])
                "."
                `obj)
               [(Term.app `to_cone [`F `c `f₂])]))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c₀
              []
              []
              ":="
              (Term.app `is_cofiltered.cone [(Term.app `bicone_mk [(Term.hole "_") `c₁ `c₂])]))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `g₁
              []
              [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `c₀.X " ⟶ " `c₁.X))]
              ":="
              (Term.app `c₀.π.app [`bicone.left]))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `g₂
              []
              [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `c₀.X " ⟶ " `c₂.X))]
              ":="
              (Term.app `c₀.π.app [`bicone.right]))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`j]
                 [(Term.typeSpec ":" `J)]
                 ","
                 («term_=_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g₁.right " ≫ " (Term.app `c.π.app [`j]))
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g₂.right " ≫ " (Term.app `c.π.app [`j])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`j]) [])
                  (group
                   (Tactic.injection
                    "injection"
                    (Term.app `c₀.π.naturality [(Term.app `bicone_hom.left [`j])])
                    ["with" ["_" `e₁]])
                   [])
                  (group
                   (Tactic.injection
                    "injection"
                    (Term.app `c₀.π.naturality [(Term.app `bicone_hom.right [`j])])
                    ["with" ["_" `e₂]])
                   [])
                  (group
                   (Mathlib.Tactic.tacticSimpa!?_
                    "simpa"
                    []
                    []
                    (Mathlib.Tactic.simpaArgsRest
                     []
                     []
                     []
                     []
                     []
                     [(Tactic.usingArg "using" (Term.app `e₁.symm.trans [`e₂]))]))
                   [])]))))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_=_» (Term.app `c.extend [`g₁.right]) "=" (Term.app `c.extend [`g₂.right])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.unfold' "unfold" [] [(group `cone.extend)] []) [])
                  (group (Tactic.congr' "congr" [(num "1")] []) [])
                  (group
                   (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))] [])
                   [])
                  (group (Tactic.apply "apply" `this) [])]))))))
           [])
          (group (Mathlib.Tactic.tacticHave_ "have" [] [(Term.typeSpec ":" («term_=_» `g₁.right "=" `g₂.right))]) [])
          (group
           (calcTactic
            "calc"
            (calcStep
             («term_=_» `g₁.right "=" (Term.app `hc.lift [(Term.app `c.extend [`g₁.right])]))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
                 (group (Tactic.tidy "tidy" []) [])]))))
            [(calcStep
              («term_=_» (Term.hole "_") "=" (Term.app `hc.lift [(Term.app `c.extend [`g₂.right])]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (choice (Tactic.congr' "congr" [] []) (Tactic.congr "congr" [])) [])
                  (group (Tactic.exact "exact" `this) [])]))))
             (calcStep
              («term_=_» (Term.hole "_") "=" `g₂.right)
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.symm "symm") [])
                  (group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
                  (group (Tactic.tidy "tidy" []) [])]))))])
           [])
          (group
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              `f₁
              "="
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
               " ≫ "
               `f₁))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₁.right])))
              ":="
              `g₁.w)
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₂.right])))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
                " ≫ "
                `f₂))
              ":="
              `g₂.w.symm)
             (calcStep
              («term_=_» (Term.hole "_") "=" `f₂)
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])]))))])
           [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         `f₁
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
          " ≫ "
          `f₁))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₁.right])))
         ":="
         `g₁.w)
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₂.right])))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
           " ≫ "
           `f₂))
         ":="
         `g₂.w.symm)
        (calcStep
         («term_=_» (Term.hole "_") "=" `f₂)
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" `f₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `g₂.w.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
        " ≫ "
        `f₂))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
       " ≫ "
       `f₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₂.right])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₂.right]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `F.map [`g₂.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `F.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c₀.X.hom
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `g₁.w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₁.right])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `c₀.X.hom " ≫ " (Term.app `F.map [`g₁.right]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `F.map [`g₁.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₁.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `F.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c₀.X.hom
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       `f₁
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
        " ≫ "
        `f₁))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
       " ≫ "
       `f₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (calcTactic
       "calc"
       (calcStep
        («term_=_» `g₁.right "=" (Term.app `hc.lift [(Term.app `c.extend [`g₁.right])]))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
            (group (Tactic.tidy "tidy" []) [])]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (Term.app `hc.lift [(Term.app `c.extend [`g₂.right])]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (choice (Tactic.congr' "congr" [] []) (Tactic.congr "congr" [])) [])
             (group (Tactic.exact "exact" `this) [])]))))
        (calcStep
         («term_=_» (Term.hole "_") "=" `g₂.right)
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.symm "symm") [])
             (group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
             (group (Tactic.tidy "tidy" []) [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.symm "symm") [])
          (group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
          (group (Tactic.tidy "tidy" []) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c.extend [(Term.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c.extend [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hc.uniq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.symm "symm")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" `g₂.right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂.right
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (choice (Tactic.congr' "congr" [] []) (Tactic.congr "congr" [])) [])
          (group (Tactic.exact "exact" `this) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `this)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (choice (Tactic.congr' "congr" [] []) (Tactic.congr "congr" []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `hc.lift [(Term.app `c.extend [`g₂.right])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hc.lift [(Term.app `c.extend [`g₂.right])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c.extend [`g₂.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c.extend [`g₂.right]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hc.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])) [])
          (group (Tactic.tidy "tidy" []) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.apply "apply" (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hc.uniq [(Term.app `c.extend [(Term.hole "_")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c.extend [(Term.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c.extend [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hc.uniq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `g₁.right "=" (Term.app `hc.lift [(Term.app `c.extend [`g₁.right])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hc.lift [(Term.app `c.extend [`g₁.right])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c.extend [`g₁.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₁.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c.extend [`g₁.right]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hc.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `g₁.right
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.tacticHave_ "have" [] [(Term.typeSpec ":" («term_=_» `g₁.right "=" `g₂.right))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `g₁.right "=" `g₂.right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂.right
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `g₁.right
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» (Term.app `c.extend [`g₁.right]) "=" (Term.app `c.extend [`g₂.right])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.unfold' "unfold" [] [(group `cone.extend)] []) [])
             (group (Tactic.congr' "congr" [(num "1")] []) [])
             (group
              (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))] [])
              [])
             (group (Tactic.apply "apply" `this) [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.unfold' "unfold" [] [(group `cone.extend)] []) [])
          (group (Tactic.congr' "congr" [(num "1")] []) [])
          (group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))] []) [])
          (group (Tactic.apply "apply" `this) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `this)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.congr' "congr" [(num "1")] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.unfold' "unfold" [] [(group `cone.extend)] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `c.extend [`g₁.right]) "=" (Term.app `c.extend [`g₂.right]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c.extend [`g₂.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `c.extend [`g₁.right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₁.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c.extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`j]
            [(Term.typeSpec ":" `J)]
            ","
            («term_=_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g₁.right " ≫ " (Term.app `c.π.app [`j]))
             "="
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g₂.right " ≫ " (Term.app `c.π.app [`j])))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.intro "intro" [`j]) [])
             (group
              (Tactic.injection
               "injection"
               (Term.app `c₀.π.naturality [(Term.app `bicone_hom.left [`j])])
               ["with" ["_" `e₁]])
              [])
             (group
              (Tactic.injection
               "injection"
               (Term.app `c₀.π.naturality [(Term.app `bicone_hom.right [`j])])
               ["with" ["_" `e₂]])
              [])
             (group
              (Mathlib.Tactic.tacticSimpa!?_
               "simpa"
               []
               []
               (Mathlib.Tactic.simpaArgsRest
                []
                []
                []
                []
                []
                [(Tactic.usingArg "using" (Term.app `e₁.symm.trans [`e₂]))]))
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.intro "intro" [`j]) [])
          (group
           (Tactic.injection
            "injection"
            (Term.app `c₀.π.naturality [(Term.app `bicone_hom.left [`j])])
            ["with" ["_" `e₁]])
           [])
          (group
           (Tactic.injection
            "injection"
            (Term.app `c₀.π.naturality [(Term.app `bicone_hom.right [`j])])
            ["with" ["_" `e₂]])
           [])
          (group
           (Mathlib.Tactic.tacticSimpa!?_
            "simpa"
            []
            []
            (Mathlib.Tactic.simpaArgsRest [] [] [] [] [] [(Tactic.usingArg "using" (Term.app `e₁.symm.trans [`e₂]))]))
           [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimpa!?_
       "simpa"
       []
       []
       (Mathlib.Tactic.simpaArgsRest [] [] [] [] [] [(Tactic.usingArg "using" (Term.app `e₁.symm.trans [`e₂]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e₁.symm.trans [`e₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e₁.symm.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.injection
       "injection"
       (Term.app `c₀.π.naturality [(Term.app `bicone_hom.right [`j])])
       ["with" ["_" `e₂]])-/-- failed to format: format: uncaught backtrack exception
theorem
  uniq
  { K : J ⥤ C }
      { c : Cone K }
      ( hc : IsLimit c )
      ( s : Cone K ⋙ F )
      ( f₁ f₂ : s . x ⟶ F . obj c . x )
      ( h₁ : ∀ j : J , f₁ ≫ F . mapCone c . π . app j = s . π . app j )
      ( h₂ : ∀ j : J , f₂ ≫ F . mapCone c . π . app j = s . π . app j )
    : f₁ = f₂
  :=
    by
      let
          α₁
            : to_diagram F.map_cone c ⋙ map f₁ ⟶ to_diagram s
            :=
            { app := fun X => eq_to_hom by simp [ ← h₁ ] , naturality' := fun _ _ _ => by ext simp }
        let
          α₂
            : to_diagram F.map_cone c ⋙ map f₂ ⟶ to_diagram s
            :=
            { app := fun X => eq_to_hom by simp [ ← h₂ ] , naturality' := fun _ _ _ => by ext simp }
        let
          c₁
            : cone to_diagram s ⋙ pre s.X K F
            :=
            cones.postcompose ( whisker_right α₁ pre s.X K F : _ ) . obj to_cone F c f₁
        let
          c₂
            : cone to_diagram s ⋙ pre s.X K F
            :=
            cones.postcompose ( whisker_right α₂ pre s.X K F : _ ) . obj to_cone F c f₂
        let c₀ := is_cofiltered.cone bicone_mk _ c₁ c₂
        let g₁ : c₀.X ⟶ c₁.X := c₀.π.app bicone.left
        let g₂ : c₀.X ⟶ c₂.X := c₀.π.app bicone.right
        have
          : ∀ j : J , g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j
            :=
            by
              intro j
                injection c₀.π.naturality bicone_hom.left j with _ e₁
                injection c₀.π.naturality bicone_hom.right j with _ e₂
                simpa using e₁.symm.trans e₂
        have : c.extend g₁.right = c.extend g₂.right := by unfold cone.extend congr 1 ext x apply this
        have : g₁.right = g₂.right
        calc
          g₁.right = hc.lift c.extend g₁.right := by apply hc.uniq c.extend _ tidy
          _ = hc.lift c.extend g₂.right := by congr congr exact this
            _ = g₂.right := by symm apply hc.uniq c.extend _ tidy
        calc
          f₁ = 𝟙 _ ≫ f₁ := by simp
          _ = c₀.X.hom ≫ F.map g₁.right := g₁.w
            _ = c₀.X.hom ≫ F.map g₂.right := by rw [ this ]
            _ = 𝟙 _ ≫ f₂ := g₂.w.symm
            _ = f₂ := by simp

end PreservesFiniteLimitsOfFlat

/-- Representably flat functors preserve finite limits. -/
noncomputable def preservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] : PreservesFiniteLimits F := by
  apply preserves_finite_limits_of_preserves_finite_limits_of_size
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  exact
    { lift := preserves_finite_limits_of_flat.lift F hc, fac' := preserves_finite_limits_of_flat.fac F hc,
      uniq' := fun s m h => by
        apply preserves_finite_limits_of_flat.uniq F hc
        exact h
        exact preserves_finite_limits_of_flat.fac F hc s }

/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
noncomputable def preservesFiniteLimitsIffFlat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ≃ PreservesFiniteLimits F where
  toFun := fun _ => preserves_finite_limits_of_flat F
  invFun := fun _ => flat_of_preserves_finite_limits F
  left_inv := fun _ => proof_irrel _ _
  right_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size
    congr

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]

/-- (Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D) [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    lan F ⋙ (evaluation D E).obj X ≅ (whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => colim.mapIso (Iso.refl _))
    (by
      intro G H i
      ext
      simp only [functor.comp_map, colimit.ι_desc_assoc, functor.map_iso_refl, evaluation_obj_map,
        whiskering_left_obj_map, category.comp_id, Lan_map_app, category.assoc]
      erw [colimit.ι_pre_assoc (Lan.diagram F H X) (costructured_arrow.map j.hom), category.id_comp, category.comp_id,
        colimit.ι_map]
      rcases j with ⟨j_left, ⟨⟨⟩⟩, j_hom⟩
      congr
      rw [costructured_arrow.map_mk, category.id_comp, costructured_arrow.mk])

variable [ConcreteCategory.{u₁} E] [HasLimits E] [HasColimits E]

variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]

variable [PreservesLimits (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable instance lanPreservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  skip
  apply preserves_limits_of_shape_of_evaluation (Lan F.op : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K))
  exact preserves_limits_of_shape_of_nat_iso (Lan_evaluation_iso_colim _ _ _).symm

instance Lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] : RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preserves_finite_limits _

variable [HasFiniteLimits C]

noncomputable instance lanPreservesFiniteLimitsOfPreservesFiniteLimits (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) := by
  haveI := flat_of_preserves_finite_limits F
  infer_instance

theorem flat_iff_Lan_flat (F : C ⥤ D) : RepresentablyFlat F ↔ RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun H => inferInstance, fun H => by
    skip
    haveI := preserves_finite_limits_of_flat (Lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    haveI : preserves_finite_limits F := by
      apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
      intros
      skip
      apply preserves_limit_of_Lan_presesrves_limit
    apply flat_of_preserves_finite_limits⟩

/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
noncomputable def preservesFiniteLimitsIffLanPreservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ≃ PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) where
  toFun := fun _ => inferInstance
  invFun := fun _ => by
    apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
    intros
    skip
    apply preserves_limit_of_Lan_presesrves_limit
  left_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size
    congr
  right_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    congr
    unfold CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits CategoryTheory.lanPreservesFiniteLimitsOfFlat
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size
    congr

end SmallCategory

end CategoryTheory

