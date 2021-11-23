import Mathbin.CategoryTheory.Limits.Creates 
import Mathbin.CategoryTheory.Over 
import Mathbin.CategoryTheory.IsConnected

/-!
# Connected limits in the over category

Shows that the forgetful functor `over B ⥤ C` creates connected limits, in particular `over B` has
any connected limit which `C` has.
-/


universe v u

noncomputable theory

open CategoryTheory CategoryTheory.Limits

variable{J : Type v}[small_category J]

variable{C : Type u}[category.{v} C]

variable{X : C}

namespace CategoryTheory.Over

namespace CreatesConnected

/--
(Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def nat_trans_in_over {B : C} (F : J ⥤ over B) : F ⋙ forget B ⟶ (CategoryTheory.Functor.const J).obj B :=
  { app := fun j => (F.obj j).Hom }

attribute [local tidy] tactic.case_bash

/--
(Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simps]
def raise_cone [is_connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget B)) : cone F :=
  { x := over.mk (c.π.app (Classical.arbitrary J) ≫ (F.obj (Classical.arbitrary J)).Hom),
    π := { app := fun j => over.hom_mk (c.π.app j) (nat_trans_from_is_connected (c.π ≫ nat_trans_in_over F) j _) } }

theorem raised_cone_lowers_to_original [is_connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget B))
  (t : is_limit c) : (forget B).mapCone (raise_cone c) = c :=
  by 
    tidy

/-- (Impl) Show that the raised cone is a limit. -/
def raised_cone_is_limit [is_connected J] {B : C} {F : J ⥤ over B} {c : cone (F ⋙ forget B)} (t : is_limit c) :
  is_limit (raise_cone c) :=
  { lift :=
      fun s =>
        over.hom_mk (t.lift ((forget B).mapCone s))
          (by 
            dsimp 
            simp ),
    uniq' :=
      fun s m K =>
        by 
          ext1 
          apply t.hom_ext 
          intro j 
          simp [←K j] }

end CreatesConnected

/-- The forgetful functor from the over category creates any connected limit. -/
instance forget_creates_connected_limits [is_connected J] {B : C} : creates_limits_of_shape J (forget B) :=
  { CreatesLimit :=
      fun K =>
        creates_limit_of_reflects_iso
          fun c t =>
            { liftedCone := creates_connected.raise_cone c,
              validLift := eq_to_iso (creates_connected.raised_cone_lowers_to_original c t),
              makesLimit := creates_connected.raised_cone_is_limit t } }

/-- The over category has any connected limit which the original category has. -/
instance has_connected_limits {B : C} [is_connected J] [has_limits_of_shape J C] : has_limits_of_shape J (over B) :=
  { HasLimit := fun F => has_limit_of_created F (forget B) }

end CategoryTheory.Over

