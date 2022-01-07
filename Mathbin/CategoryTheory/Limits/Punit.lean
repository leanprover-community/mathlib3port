import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `discrete punit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `discrete punit` has all
(co)limits.
-/


universe v

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type v} [small_category J] {F : J ⥤ discrete PUnit.{v + 1}}

/-- A trivial cone for a functor into `punit`. `punit_cone_is_limit` shows it is a limit. -/
def punit_cone : cone F :=
  ⟨PUnit.unit, (functor.punit_ext _ _).Hom⟩

/-- A trivial cocone for a functor into `punit`. `punit_cocone_is_limit` shows it is a colimit. -/
def punit_cocone : cocone F :=
  ⟨PUnit.unit, (functor.punit_ext _ _).Hom⟩

/-- Any cone over a functor into `punit` is a limit cone.
-/
def punit_cone_is_limit {c : cone F} : is_limit c := by
  tidy

/-- Any cocone over a functor into `punit` is a colimit cocone.
-/
def punit_cocone_is_colimit {c : cocone F} : is_colimit c := by
  tidy

instance : has_limits (discrete PUnit) := by
  tidy

instance : has_colimits (discrete PUnit) := by
  tidy

end CategoryTheory.Limits

