import Mathbin.Algebra.Category.Group.ZModuleEquivalence
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.Category.Group.Colimits
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.CategoryTheory.Abelian.Basic

/-!
# The category of abelian groups is abelian
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGroupₓₓ

section

variable {X Y : AddCommGroupₓₓ.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono (hf : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv <|
    ModuleCat.normalMono _ <| right_adjoint_preserves_mono (Functor.adjunction _) hf

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi (hf : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv <|
    ModuleCat.normalEpi _ <| left_adjoint_preserves_epi (Functor.adjunction _) hf

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupₓₓ.{u} where
  HasFiniteProducts :=
    ⟨by
      infer_instance⟩
  normalMonoOfMono := fun X Y => normalMono
  normalEpiOfEpi := fun X Y => normalEpi
  add_comp' := by
    intros
    simp only [preadditive.add_comp]
  comp_add' := by
    intros
    simp only [preadditive.comp_add]

end AddCommGroupₓₓ

