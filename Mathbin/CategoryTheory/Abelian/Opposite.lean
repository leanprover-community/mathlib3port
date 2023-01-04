/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.opposite
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.CategoryTheory.Limits.Opposites

/-!
# The opposite of an abelian category is abelian.
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type _) [Category C] [Abelian C]

attribute [local instance]
  has_finite_limits_of_has_equalizers_and_finite_products has_finite_colimits_of_has_coequalizers_and_finite_coproducts

instance : Abelian Cᵒᵖ
    where
  normalMonoOfMono X Y f m := normal_mono_of_normal_epi_unop _ (normal_epi_of_epi f.unop)
  normalEpiOfEpi X Y f m := normal_epi_of_normal_mono_unop _ (normal_mono_of_mono f.unop)

section

variable {C} {X Y : C} (f : X ⟶ Y) {A B : Cᵒᵖ} (g : A ⟶ B)

-- TODO: Generalize (this will work whenever f has a cokernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernelOpUnop : (kernel f.op).unop ≅ cokernel f
    where
  Hom := (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
    cokernel.desc f (kernel.ι f.op).unop <|
      by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  hom_inv_id' := by
    rw [← unop_id, ← (cokernel.desc f _ _).unop_op, ← unop_comp]
    congr 1
    dsimp
    ext
    simp [← op_comp]
  inv_hom_id' := by
    dsimp
    ext
    simp [← unop_comp]
#align category_theory.kernel_op_unop CategoryTheory.kernelOpUnop

-- TODO: Generalize (this will work whenever f has a kernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernelOpUnop : (cokernel f.op).unop ≅ kernel f
    where
  Hom :=
    kernel.lift f (cokernel.π f.op).unop <|
      by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id' := by
    rw [← unop_id, ← (kernel.lift f _ _).unop_op, ← unop_comp]
    congr 1
    dsimp
    ext
    simp [← op_comp]
  inv_hom_id' := by
    dsimp
    ext
    simp [← unop_comp]
#align category_theory.cokernel_op_unop CategoryTheory.cokernelOpUnop

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernelOpUnop g.unop).op
#align category_theory.kernel_unop_op CategoryTheory.kernelUnopOp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernelOpUnop g.unop).op
#align category_theory.cokernel_unop_op CategoryTheory.cokernelUnopOp

theorem Cokernel.π_op :
    (cokernel.π f.op).unop =
      (cokernelOpUnop f).Hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm :=
  by simp [cokernel_op_unop]
#align category_theory.cokernel.π_op CategoryTheory.Cokernel.π_op

theorem Kernel.ι_op :
    (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpUnop f).inv := by
  simp [kernel_op_unop]
#align category_theory.kernel.ι_op CategoryTheory.Kernel.ι_op

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernelOpUnop f).op.symm
#align category_theory.kernel_op_op CategoryTheory.kernelOpOp

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernelOpUnop f).op.symm
#align category_theory.cokernel_op_op CategoryTheory.cokernelOpOp

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop :=
  (kernelUnopOp g).unop.symm
#align category_theory.kernel_unop_unop CategoryTheory.kernelUnopUnop

theorem Kernel.ι_unop :
    (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv := by
  simp
#align category_theory.kernel.ι_unop CategoryTheory.Kernel.ι_unop

theorem Cokernel.π_unop :
    (cokernel.π g.unop).op =
      (cokernelUnopOp g).Hom ≫ kernel.ι g ≫ eqToHom (Opposite.op_unop _).symm :=
  by simp
#align category_theory.cokernel.π_unop CategoryTheory.Cokernel.π_unop

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernelUnopOp g).unop.symm
#align category_theory.cokernel_unop_unop CategoryTheory.cokernelUnopUnop

end

end CategoryTheory

