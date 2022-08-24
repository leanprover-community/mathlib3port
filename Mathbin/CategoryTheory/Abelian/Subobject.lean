/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Abelian.Opposite
import Mathbin.CategoryTheory.Subobject.Limits

/-!
# Equivalence between subobjects and quotients in an abelian category

-/


open CategoryTheory CategoryTheory.Limits Opposite

universe v u

noncomputable section

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

/-- In an abelian category, the subobjects and quotient objects of an object `X` are
    order-isomorphic via taking kernels and cokernels.
    Implemented here using subobjects in the opposite category,
    since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps]
def subobjectIsoSubobjectOp [Abelian C] (X : C) : Subobject X ≃o (Subobject (op X))ᵒᵈ := by
  refine' OrderIso.ofHomInv (cokernel_order_hom X) (kernel_order_hom X) _ _
  · change (cokernel_order_hom X).comp (kernel_order_hom X) = _
    refine' OrderHom.ext _ _ (funext (subobject.ind _ _))
    intro A f hf
    dsimp' only [OrderHom.comp_coe, Function.comp_app, kernel_order_hom_coe, subobject.lift_mk, cokernel_order_hom_coe,
      OrderHom.id_coe, id.def]
    refine' subobject.mk_eq_mk_of_comm _ _ ⟨_, _, Quiver.Hom.unop_inj _, Quiver.Hom.unop_inj _⟩ _
    · exact (abelian.epi_desc f.unop _ (cokernel.condition (kernel.ι f.unop))).op
      
    · exact (cokernel.desc _ _ (kernel.condition f.unop)).op
      
    · simp only [← cancel_epi (cokernel.π (kernel.ι f.unop)), unop_comp, Quiver.Hom.unop_op, unop_id_op,
        cokernel.π_desc_assoc, comp_epi_desc, category.comp_id]
      
    · simp only [← cancel_epi f.unop, unop_comp, Quiver.Hom.unop_op, unop_id, comp_epi_desc_assoc, cokernel.π_desc,
        category.comp_id]
      
    · exact
        Quiver.Hom.unop_inj
          (by
            simp only [unop_comp, Quiver.Hom.unop_op, comp_epi_desc])
      
    
  · change (kernel_order_hom X).comp (cokernel_order_hom X) = _
    refine' OrderHom.ext _ _ (funext (subobject.ind _ _))
    intro A f hf
    dsimp' only [OrderHom.comp_coe, Function.comp_app, cokernel_order_hom_coe, subobject.lift_mk, kernel_order_hom_coe,
      OrderHom.id_coe, id.def, unop_op, Quiver.Hom.unop_op]
    refine' subobject.mk_eq_mk_of_comm _ _ ⟨_, _, _, _⟩ _
    · exact abelian.mono_lift f _ (kernel.condition (cokernel.π f))
      
    · exact kernel.lift _ _ (cokernel.condition f)
      
    · simp only [← cancel_mono (kernel.ι (cokernel.π f)), category.assoc, image.fac, mono_lift_comp, category.id_comp,
        auto_param_eq]
      
    · simp only [← cancel_mono f, category.assoc, mono_lift_comp, image.fac, category.id_comp, auto_param_eq]
      
    · simp only [mono_lift_comp]
      
    

/-- A well-powered abelian category is also well-copowered. -/
instance well_powered_opposite [Abelian C] [WellPowered C] :
    WellPowered
      Cᵒᵖ where subobject_small := fun X => (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

end CategoryTheory.Abelian

