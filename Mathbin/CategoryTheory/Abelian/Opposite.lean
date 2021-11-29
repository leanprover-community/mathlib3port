import Mathbin.CategoryTheory.Abelian.Basic 
import Mathbin.CategoryTheory.Preadditive.Opposite 
import Mathbin.CategoryTheory.Limits.Opposites 
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# The opposite of an abelian category is abelian.
-/


noncomputable theory

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type _) [category C] [abelian C]

attribute [local instance] finite_limits_from_equalizers_and_finite_products
  finite_colimits_from_coequalizers_and_finite_coproducts has_finite_limits_opposite has_finite_colimits_opposite
  has_finite_products_opposite

instance : abelian («expr ᵒᵖ» C) :=
  { NormalMono :=
      fun X Y f m =>
        by 
          exact normal_mono_of_normal_epi_unop _ (abelian.normal_epi f.unop),
    NormalEpi :=
      fun X Y f m =>
        by 
          exact normal_epi_of_normal_mono_unop _ (abelian.normal_mono f.unop) }

section 

variable {C} {X Y : C} (f : X ⟶ Y) {A B : «expr ᵒᵖ» C} (g : A ⟶ B)

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernel_op_unop : (kernel f.op).unop ≅ cokernel f :=
  { Hom :=
      (kernel.lift f.op (cokernel.π f).op$
          by 
            simp [←op_comp]).unop,
    inv :=
      cokernel.desc f (kernel.ι f.op).unop$
        by 
          rw [←f.unop_op, ←unop_comp, f.unop_op]
          simp ,
    hom_inv_id' :=
      by 
        rw [←unop_id, ←(cokernel.desc f _ _).unop_op, ←unop_comp]
        congr 1
        dsimp 
        ext 
        simp [←op_comp],
    inv_hom_id' :=
      by 
        dsimp 
        ext 
        simp [←unop_comp] }

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernel_op_unop : (cokernel f.op).unop ≅ kernel f :=
  { Hom :=
      kernel.lift f (cokernel.π f.op).unop$
        by 
          rw [←f.unop_op, ←unop_comp, f.unop_op]
          simp ,
    inv :=
      (cokernel.desc f.op (kernel.ι f).op$
          by 
            simp [←op_comp]).unop,
    hom_inv_id' :=
      by 
        rw [←unop_id, ←(kernel.lift f _ _).unop_op, ←unop_comp]
        congr 1
        dsimp 
        ext 
        simp [←op_comp],
    inv_hom_id' :=
      by 
        dsimp 
        ext 
        simp [←unop_comp] }

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernel_unop_op : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernel_op_unop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernel_unop_op : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernel_op_unop g.unop).op

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernel_op_op : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernel_op_unop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernel_op_op : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernel_op_unop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernel_unop_unop : kernel g.unop ≅ (cokernel g).unop :=
  (kernel_unop_op g).unop.symm

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernel_unop_unop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernel_unop_op g).unop.symm

end 

end CategoryTheory

