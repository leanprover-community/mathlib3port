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

noncomputable theory

namespace AddCommGroupₓₓ

section 

variable {X Y : AddCommGroupₓₓ.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono (hf : mono f) : normal_mono f :=
  equivalence_reflects_normal_mono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv$
    ModuleCat.normalMono _$ right_adjoint_preserves_mono (functor.adjunction _) hf

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi (hf : epi f) : normal_epi f :=
  equivalence_reflects_normal_epi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv$
    ModuleCat.normalEpi _$ left_adjoint_preserves_epi (functor.adjunction _) hf

end 

/-- The category of abelian groups is abelian. -/
instance : abelian AddCommGroupₓₓ.{u} :=
  { HasFiniteProducts :=
      ⟨by 
          infer_instance⟩,
    NormalMono := fun X Y => normal_mono, NormalEpi := fun X Y => normal_epi,
    add_comp' :=
      by 
        intros 
        simp only [preadditive.add_comp],
    comp_add' :=
      by 
        intros 
        simp only [preadditive.comp_add] }

end AddCommGroupₓₓ

