import Mathbin.Topology.Sheaves.SheafCondition.Sites 
import Mathbin.CategoryTheory.Sites.Limits 
import Mathbin.CategoryTheory.Adjunction.Default 
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable theory

universe v u

open CategoryTheory

open CategoryTheory.Limits

variable{C : Type u}[category.{v} C]{J : Type v}[small_category J]

namespace Top

instance  [has_limits C] (X : Top) : has_limits (presheaf C X) :=
  by 
    dsimp [presheaf]
    infer_instance

instance  [has_colimits C] (X : Top) : has_colimits (presheaf C X) :=
  by 
    dsimp [presheaf]
    infer_instance

instance  [has_limits C] (X : Top) : creates_limits (sheaf.forget C X) :=
  (@creates_limits_of_nat_iso _ _ (presheaf.Sheaf_spaces_equiv_sheaf_sites_inverse_forget C X))
    (@CategoryTheory.compCreatesLimits _ _ _ _ _ _
      Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{u, v, v})

instance  [has_limits C] (X : Top) : has_limits (sheaf C X) :=
  has_limits_of_has_limits_creates_limits (sheaf.forget C X)

theorem is_sheaf_of_is_limit [has_limits C] {X : Top} (F : J ⥤ presheaf C X) (H : ∀ j, (F.obj j).IsSheaf) {c : cone F}
  (hc : is_limit c) : c.X.is_sheaf :=
  by 
    let F' : J ⥤ sheaf C X := { obj := fun j => ⟨F.obj j, H j⟩, map := F.map }
    let e : F' ⋙ sheaf.forget C X ≅ F :=
      nat_iso.of_components (fun _ => iso.refl _)
        (by 
          tidy)
    exact
      presheaf.is_sheaf_of_iso
        ((is_limit_of_preserves (sheaf.forget C X) (limit.is_limit F')).conePointsIsoOfNatIso hc e) (limit F').2

theorem limit_is_sheaf [has_limits C] {X : Top} (F : J ⥤ presheaf C X) (H : ∀ j, (F.obj j).IsSheaf) :
  (limit F).IsSheaf :=
  is_sheaf_of_is_limit F H (limit.is_limit F)

end Top

