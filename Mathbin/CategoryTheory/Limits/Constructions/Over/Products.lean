import Mathbin.CategoryTheory.Over 
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_wide_pullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `over B` has `J`-indexed products.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable{J : Type v}

variable{C : Type u}[category.{v} C]

variable{X : C}

namespace CategoryTheory.Over

namespace ConstructProducts

/--
(Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
@[reducible]
def wide_pullback_diagram_of_diagram_over (B : C) {J : Type v} (F : discrete J ⥤ over B) : wide_pullback_shape J ⥤ C :=
  wide_pullback_shape.wide_cospan B (fun j => (F.obj j).left) fun j => (F.obj j).Hom

-- error in CategoryTheory.Limits.Constructions.Over.Products: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps #[]]
def cones_equiv_inverse_obj
(B : C)
{J : Type v}
(F : «expr ⥤ »(discrete J, over B))
(c : cone F) : cone (wide_pullback_diagram_of_diagram_over B F) :=
{ X := c.X.left,
  π := { app := λ X, option.cases_on X c.X.hom (λ j : J, (c.π.app j).left),
    naturality' := λ X Y f, begin
      dsimp [] [] [] [],
      cases [expr X] []; cases [expr Y] []; cases [expr f] [],
      { rw ["[", expr category.id_comp, ",", expr category.comp_id, "]"] [] },
      { rw ["[", expr over.w, ",", expr category.id_comp, "]"] [] },
      { rw ["[", expr category.id_comp, ",", expr category.comp_id, "]"] [] }
    end } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_inverse (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone F ⥤ cone (wide_pullback_diagram_of_diagram_over B F) :=
  { obj := cones_equiv_inverse_obj B F,
    map :=
      fun c₁ c₂ f =>
        { Hom := f.hom.left,
          w' :=
            fun j =>
              by 
                cases j
                ·
                  simp 
                ·
                  dsimp 
                  rw [←f.w j]
                  rfl } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_functor (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone (wide_pullback_diagram_of_diagram_over B F) ⥤ cone F :=
  { obj :=
      fun c =>
        { x := over.mk (c.π.app none),
          π :=
            { app :=
                fun j =>
                  over.hom_mk (c.π.app (some j))
                    (by 
                      apply c.w (wide_pullback_shape.hom.term j)) } },
    map := fun c₁ c₂ f => { Hom := over.hom_mk f.hom } }

attribute [local tidy] tactic.case_bash

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_unit_iso (B : C) (F : discrete J ⥤ over B) :
  𝟭 (cone (wide_pullback_diagram_of_diagram_over B F)) ≅ cones_equiv_functor B F ⋙ cones_equiv_inverse B F :=
  nat_iso.of_components
    (fun _ =>
      cones.ext { Hom := 𝟙 _, inv := 𝟙 _ }
        (by 
          tidy))
    (by 
      tidy)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_counit_iso (B : C) (F : discrete J ⥤ over B) :
  cones_equiv_inverse B F ⋙ cones_equiv_functor B F ≅ 𝟭 (cone F) :=
  nat_iso.of_components
    (fun _ =>
      cones.ext { Hom := over.hom_mk (𝟙 _), inv := over.hom_mk (𝟙 _) }
        (by 
          tidy))
    (by 
      tidy)

/--
(Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
def cones_equiv (B : C) (F : discrete J ⥤ over B) : cone (wide_pullback_diagram_of_diagram_over B F) ≌ cone F :=
  { Functor := cones_equiv_functor B F, inverse := cones_equiv_inverse B F, unitIso := cones_equiv_unit_iso B F,
    counitIso := cones_equiv_counit_iso B F }

/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_wide_pullback_limit {B : C} (F : discrete J ⥤ over B)
  [has_limit (wide_pullback_diagram_of_diagram_over B F)] : has_limit F :=
  has_limit.mk
    { Cone := _,
      IsLimit :=
        is_limit.of_right_adjoint (cones_equiv B F).Functor
          (limit.is_limit (wide_pullback_diagram_of_diagram_over B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_wide_pullback [has_limits_of_shape (wide_pullback_shape J) C] {B : C} :
  has_limits_of_shape (discrete J) (over B) :=
  { HasLimit := fun F => has_over_limit_discrete_of_wide_pullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binary_product_of_pullback [has_pullbacks C] {B : C} : has_binary_products (over B) :=
  over_product_of_wide_pullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_wide_pullbacks [has_wide_pullbacks C] {B : C} : has_products (over B) :=
  fun J => over_product_of_wide_pullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finite_products_of_finite_wide_pullbacks [has_finite_wide_pullbacks C] {B : C} :
  has_finite_products (over B) :=
  ⟨fun J 𝒥₁ 𝒥₂ =>
      by 
        exact over_product_of_wide_pullback⟩

end ConstructProducts

-- error in CategoryTheory.Limits.Constructions.Over.Products: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_wide_pullback` above.)
-/ theorem over_has_terminal (B : C) : has_terminal (over B) :=
{ has_limit := λ
  F, has_limit.mk { cone := { X := over.mk («expr𝟙»() _), π := { app := λ p, pempty.elim p } },
    is_limit := { lift := λ s, over.hom_mk _,
      fac' := λ _ j, j.elim,
      uniq' := λ s m _, begin
        ext [] [] [],
        rw [expr over.hom_mk_left] [],
        have [] [] [":=", expr m.w],
        dsimp [] [] [] ["at", ident this],
        rwa ["[", expr category.comp_id, ",", expr category.comp_id, "]"] ["at", ident this]
      end } } }

end CategoryTheory.Over

