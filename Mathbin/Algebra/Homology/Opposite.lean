/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston

! This file was ported from Lean 3 source module algebra.homology.opposite
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Opposite
import Mathbin.CategoryTheory.Abelian.Homology
import Mathbin.Algebra.Homology.Additive

/-!
# Opposite categories of complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analagous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analagous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `op_symm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/


noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

section

variable {V : Type _} [Category V] [Abelian V]

/- warning: image_to_kernel_op -> imageToKernel_op is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_op imageToKernel_opₓ'. -/
theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).Hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv :=
  by
  ext
  simpa only [iso.trans_hom, iso.symm_hom, iso.trans_inv, kernel_op_op_inv, category.assoc,
    imageToKernel_arrow, kernel_subobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc, ←
    image_subobject_arrow, ← image_unop_op_inv_comp_op_factor_thru_image g.op]
#align image_to_kernel_op imageToKernel_op

/- warning: image_to_kernel_unop -> imageToKernel_unop is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_unop imageToKernel_unopₓ'. -/
theorem imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) =
      (imageSubobjectIso _ ≪≫ (imageUnopUnop _).symm).Hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), category.assoc, image.fac, w, zero_comp])).unop ≫
          (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv :=
  by
  ext
  dsimp only [image_unop_unop]
  simp only [iso.trans_hom, iso.symm_hom, iso.trans_inv, kernel_unop_unop_inv, category.assoc,
    imageToKernel_arrow, kernel_subobject_arrow', kernel.lift_ι, cokernel.π_desc, iso.unop_inv, ←
    unop_comp, factor_thru_image_comp_image_unop_op_inv, Quiver.Hom.unop_op, image_subobject_arrow]
#align image_to_kernel_unop imageToKernel_unop

#print homologyOp /-
/-- Given `f, g` with `f ≫ g = 0`, the homology of `g.op, f.op` is the opposite of the homology of
`f, g`. -/
def homologyOp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology g.op f.op (by rw [← op_comp, w, op_zero]) ≅ Opposite.op (homology f g w) :=
  cokernelIsoOfEq (imageToKernel_op _ _ w) ≪≫
    cokernelEpiComp _ _ ≪≫
      cokernelCompIsIso _ _ ≪≫
        cokernelOpOp _ ≪≫
          (homologyIsoKernelDesc _ _ _ ≪≫
              kernelIsoOfEq
                  (by ext <;> simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]) ≪≫
                kernelCompMono _ (image.ι g)).op
#align homology_op homologyOp
-/

#print homologyUnop /-
/-- Given morphisms `f, g` in `Vᵒᵖ` with `f ≫ g = 0`, the homology of `g.unop, f.unop` is the
opposite of the homology of `f, g`. -/
def homologyUnop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology g.unop f.unop (by rw [← unop_comp, w, unop_zero]) ≅ Opposite.unop (homology f g w) :=
  cokernelIsoOfEq (imageToKernel_unop _ _ w) ≪≫
    cokernelEpiComp _ _ ≪≫
      cokernelCompIsIso _ _ ≪≫
        cokernelUnopUnop _ ≪≫
          (homologyIsoKernelDesc _ _ _ ≪≫
              kernelIsoOfEq
                  (by ext <;> simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]) ≪≫
                kernelCompMono _ (image.ι g)).unop
#align homology_unop homologyUnop
-/

end

namespace HomologicalComplex

variable {ι V : Type _} [Category V] {c : ComplexShape ι}

section

variable [Preadditive V]

#print HomologicalComplex.op /-
/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm
    where
  pt i := op (X.pt i)
  d i j := (X.d j i).op
  shape' i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' := by
    intros
    rw [← op_comp, X.d_comp_d, op_zero]
#align homological_complex.op HomologicalComplex.op
-/

#print HomologicalComplex.opSymm /-
/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def opSymm (X : HomologicalComplex V c.symm) : HomologicalComplex Vᵒᵖ c
    where
  pt i := op (X.pt i)
  d i j := (X.d j i).op
  shape' i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' := by
    intros
    rw [← op_comp, X.d_comp_d, op_zero]
#align homological_complex.op_symm HomologicalComplex.opSymm
-/

#print HomologicalComplex.unop /-
/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unop (X : HomologicalComplex Vᵒᵖ c) : HomologicalComplex V c.symm
    where
  pt i := unop (X.pt i)
  d i j := (X.d j i).unop
  shape' i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' := by
    intros
    rw [← unop_comp, X.d_comp_d, unop_zero]
#align homological_complex.unop HomologicalComplex.unop
-/

#print HomologicalComplex.unopSymm /-
/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unopSymm (X : HomologicalComplex Vᵒᵖ c.symm) : HomologicalComplex V c
    where
  pt i := unop (X.pt i)
  d i j := (X.d j i).unop
  shape' i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' := by
    intros
    rw [← unop_comp, X.d_comp_d, unop_zero]
#align homological_complex.unop_symm HomologicalComplex.unopSymm
-/

variable (V c)

#print HomologicalComplex.opFunctor /-
/-- Auxilliary definition for `op_equivalence`. -/
@[simps]
def opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm
    where
  obj X := (unop X).op
  map X Y f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j hij => by simp only [op_d, ← op_comp, f.unop.comm] }
#align homological_complex.op_functor HomologicalComplex.opFunctor
-/

#print HomologicalComplex.opInverse /-
/-- Auxilliary definition for `op_equivalence`. -/
@[simps]
def opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ
    where
  obj X := op X.unopSymm
  map X Y f :=
    Quiver.Hom.op
      { f := fun i => (f.f i).unop
        comm' := fun i j hij => by simp only [unop_symm_d, ← unop_comp, f.comm] }
#align homological_complex.op_inverse HomologicalComplex.opInverse
-/

#print HomologicalComplex.opUnitIso /-
/-- Auxilliary definition for `op_equivalence`. -/
def opUnitIso : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j hij => by
            simp only [iso.refl_hom, category.id_comp, unop_symm_d, op_d, Quiver.Hom.unop_op,
              category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine' Quiver.Hom.unop_inj _
      ext
      simp only [Quiver.Hom.unop_op, functor.id_map, iso.op_hom, functor.comp_map, unop_comp,
        comp_f, hom.iso_of_components_hom_f]
      erw [category.id_comp, category.comp_id (f.unop.f x)])
#align homological_complex.op_unit_iso HomologicalComplex.opUnitIso
-/

#print HomologicalComplex.opCounitIso /-
/-- Auxilliary definition for `op_equivalence`. -/
def opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm) :=
  NatIso.ofComponents
    (fun X =>
      HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j hij => by
        simpa only [iso.refl_hom, category.id_comp, category.comp_id] )
    (by
      intro X Y f
      ext
      simpa only [Quiver.Hom.unop_op, Quiver.Hom.op_unop, functor.comp_map, functor.id_map,
        iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f] )
#align homological_complex.op_counit_iso HomologicalComplex.opCounitIso
-/

/- warning: homological_complex.op_equivalence -> HomologicalComplex.opEquivalence is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u2} V] (c : ComplexShape.{u1} ι) [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Equivalence.{max u1 u3, max u1 u3, max u2 u1 u3, max u2 u1 u3} (Opposite.{succ (max u2 u1 u3)} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (CategoryTheory.Category.opposite.{max u1 u3, max u2 u1 u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c))
but is expected to have type
  forall {ι : Type.{u1}} (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u2} V] (c : ComplexShape.{u1} ι) [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Equivalence.{max u1 u3, max u1 u3, max (max u1 u2) u3, max (max u1 u2) u3} (Opposite.{max (max (succ u1) (succ u2)) (succ u3)} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max (max u1 u2) u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c))
Case conversion may be inaccurate. Consider using '#align homological_complex.op_equivalence HomologicalComplex.opEquivalenceₓ'. -/
/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps]
def opEquivalence : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm
    where
  Functor := opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp' := by
    intro X
    ext
    simp only [op_unit_iso, op_counit_iso, nat_iso.of_components_hom_app, iso.op_hom, comp_f,
      op_functor_map_f, Quiver.Hom.unop_op, hom.iso_of_components_hom_f]
    exact category.comp_id _
#align homological_complex.op_equivalence HomologicalComplex.opEquivalence

#print HomologicalComplex.unopFunctor /-
/-- Auxilliary definition for `unop_equivalence`. -/
@[simps]
def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm
    where
  obj X := (unop X).unop
  map X Y f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j hij => by simp only [unop_d, ← unop_comp, f.unop.comm] }
#align homological_complex.unop_functor HomologicalComplex.unopFunctor
-/

#print HomologicalComplex.unopInverse /-
/-- Auxilliary definition for `unop_equivalence`. -/
@[simps]
def unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ
    where
  obj X := op X.opSymm
  map X Y f :=
    Quiver.Hom.op
      { f := fun i => (f.f i).op
        comm' := fun i j hij => by simp only [op_symm_d, ← op_comp, f.comm] }
#align homological_complex.unop_inverse HomologicalComplex.unopInverse
-/

#print HomologicalComplex.unopUnitIso /-
/-- Auxilliary definition for `unop_equivalence`. -/
def unopUnitIso : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j hij => by
            simp only [iso.refl_hom, category.id_comp, unop_symm_d, op_d, Quiver.Hom.unop_op,
              category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine' Quiver.Hom.unop_inj _
      ext
      simp only [Quiver.Hom.unop_op, functor.id_map, iso.op_hom, functor.comp_map, unop_comp,
        comp_f, hom.iso_of_components_hom_f]
      erw [category.id_comp, category.comp_id (f.unop.f x)])
#align homological_complex.unop_unit_iso HomologicalComplex.unopUnitIso
-/

#print HomologicalComplex.unopCounitIso /-
/-- Auxilliary definition for `unop_equivalence`. -/
def unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm) :=
  NatIso.ofComponents
    (fun X =>
      HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j hij => by
        simpa only [iso.refl_hom, category.id_comp, category.comp_id] )
    (by
      intro X Y f
      ext
      simpa only [Quiver.Hom.unop_op, Quiver.Hom.op_unop, functor.comp_map, functor.id_map,
        iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f] )
#align homological_complex.unop_counit_iso HomologicalComplex.unopCounitIso
-/

/- warning: homological_complex.unop_equivalence -> HomologicalComplex.unopEquivalence is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u2} V] (c : ComplexShape.{u1} ι) [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Equivalence.{max u1 u3, max u1 u3, max u2 u1 u3, max u2 u1 u3} (Opposite.{succ (max u2 u1 u3)} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (CategoryTheory.Category.opposite.{max u1 u3, max u2 u1 u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c))
but is expected to have type
  forall {ι : Type.{u1}} (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u2} V] (c : ComplexShape.{u1} ι) [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Equivalence.{max u1 u3, max u1 u3, max (max u2 u1) u3, max (max u1 u2) u3} (Opposite.{max (max (succ u1) (succ u2)) (succ u3)} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max (max u1 u2) u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c))
Case conversion may be inaccurate. Consider using '#align homological_complex.unop_equivalence HomologicalComplex.unopEquivalenceₓ'. -/
/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps]
def unopEquivalence : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.symm
    where
  Functor := unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp' := by
    intro X
    ext
    simp only [op_unit_iso, op_counit_iso, nat_iso.of_components_hom_app, iso.op_hom, comp_f,
      op_functor_map_f, Quiver.Hom.unop_op, hom.iso_of_components_hom_f]
    exact category.comp_id _
#align homological_complex.unop_equivalence HomologicalComplex.unopEquivalence

variable {V c}

/- warning: homological_complex.op_functor_additive -> HomologicalComplex.opFunctor_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} V] {c : ComplexShape.{u1} ι} [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Functor.Additive.{max u2 u1 u3, max u2 u1 u3, max u1 u3, max u1 u3} (Opposite.{succ (max u2 u1 u3)} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max u2 u1 u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Opposite.preadditive.{max u2 u1 u3, max u1 u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.preadditive.{u3, u2, u1} ι V _inst_1 _inst_2 c)) (HomologicalComplex.CategoryTheory.preadditive.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u3} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.opFunctor.{u1, u2, u3} ι V _inst_1 c _inst_2)
but is expected to have type
  forall {ι : Type.{u1}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} V] {c : ComplexShape.{u1} ι} [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Functor.Additive.{max (max u1 u2) u3, max (max u1 u2) u3, max u1 u3, max u1 u3} (Opposite.{max (max (succ u1) (succ u2)) (succ u3)} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max (max u1 u2) u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c)) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.instPreadditiveOppositeOpposite.{max (max u1 u2) u3, max u1 u3} (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 _inst_2 c)) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u3} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.opFunctor.{u1, u2, u3} ι V _inst_1 c _inst_2)
Case conversion may be inaccurate. Consider using '#align homological_complex.op_functor_additive HomologicalComplex.opFunctor_additiveₓ'. -/
instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where
#align homological_complex.op_functor_additive HomologicalComplex.opFunctor_additive

/- warning: homological_complex.unop_functor_additive -> HomologicalComplex.unopFunctor_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} V] {c : ComplexShape.{u1} ι} [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Functor.Additive.{max u2 u1 u3, max u2 u1 u3, max u1 u3, max u1 u3} (Opposite.{succ (max u2 u1 u3)} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max u2 u1 u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Opposite.preadditive.{max u2 u1 u3, max u1 u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.preadditive.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u3} V _inst_1 _inst_2) c)) (HomologicalComplex.CategoryTheory.preadditive.{u3, u2, u1} ι V _inst_1 _inst_2 (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.unopFunctor.{u1, u2, u3} ι V _inst_1 c _inst_2)
but is expected to have type
  forall {ι : Type.{u1}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} V] {c : ComplexShape.{u1} ι} [_inst_2 : CategoryTheory.Preadditive.{u3, u2} V _inst_1], CategoryTheory.Functor.Additive.{max (max u1 u2) u3, max (max u1 u2) u3, max u1 u3, max u1 u3} (Opposite.{max (max (succ u1) (succ u2)) (succ u3)} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.Category.opposite.{max u1 u3, max (max u1 u2) u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c)) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2) (ComplexShape.symm.{u1} ι c)) (CategoryTheory.instPreadditiveOppositeOpposite.{max (max u1 u2) u3, max u1 u3} (HomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u3, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u2} V _inst_1 _inst_2)) c) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u3, u2, u1} ι (Opposite.{succ u2} V) (CategoryTheory.Category.opposite.{u3, u2} V _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u3} V _inst_1 _inst_2) c)) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u3, u2, u1} ι V _inst_1 _inst_2 (ComplexShape.symm.{u1} ι c)) (HomologicalComplex.unopFunctor.{u1, u2, u3} ι V _inst_1 c _inst_2)
Case conversion may be inaccurate. Consider using '#align homological_complex.unop_functor_additive HomologicalComplex.unopFunctor_additiveₓ'. -/
instance unopFunctor_additive : (@unopFunctor ι V _ c _).Additive where
#align homological_complex.unop_functor_additive HomologicalComplex.unopFunctor_additive

end

variable [Abelian V] (C : HomologicalComplex V c) (i : ι)

#print HomologicalComplex.homologyOpDef /-
/-- Auxilliary tautological definition for `homology_op`. -/
def homologyOpDef :
    C.op.homology i ≅
      homology (C.dFrom i).op (C.dTo i).op (by rw [← op_comp, C.d_to_comp_d_from i, op_zero]) :=
  Iso.refl _
#align homological_complex.homology_op_def HomologicalComplex.homologyOpDef
-/

#print HomologicalComplex.homologyOp /-
/-- Given a complex `C` of objects in `V`, the `i`th homology of its 'opposite' complex (with
objects in `Vᵒᵖ`) is the opposite of the `i`th homology of `C`. -/
def homologyOp : C.op.homology i ≅ Opposite.op (C.homology i) :=
  homologyOpDef _ _ ≪≫ homologyOp _ _ _
#align homological_complex.homology_op HomologicalComplex.homologyOp
-/

#print HomologicalComplex.homologyUnopDef /-
/-- Auxilliary tautological definition for `homology_unop`. -/
def homologyUnopDef (C : HomologicalComplex Vᵒᵖ c) :
    C.unop.homology i ≅
      homology (C.dFrom i).unop (C.dTo i).unop
        (by rw [← unop_comp, C.d_to_comp_d_from i, unop_zero]) :=
  Iso.refl _
#align homological_complex.homology_unop_def HomologicalComplex.homologyUnopDef
-/

#print HomologicalComplex.homologyUnop /-
/-- Given a complex `C` of objects in `Vᵒᵖ`, the `i`th homology of its 'opposite' complex (with
objects in `V`) is the opposite of the `i`th homology of `C`. -/
def homologyUnop (C : HomologicalComplex Vᵒᵖ c) :
    C.unop.homology i ≅ Opposite.unop (C.homology i) :=
  homologyUnopDef _ _ ≪≫ homologyUnop _ _ _
#align homological_complex.homology_unop HomologicalComplex.homologyUnop
-/

end HomologicalComplex

