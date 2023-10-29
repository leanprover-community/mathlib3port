/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston
-/
import CategoryTheory.Abelian.Opposite
import CategoryTheory.Abelian.Homology
import Algebra.Homology.Additive

#align_import algebra.homology.opposite from "leanprover-community/mathlib"@"50251fd6309cca5ca2e747882ffecd2729f38c5d"

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

#print imageToKernel_op /-
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
-/

#print imageToKernel_unop /-
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
-/

#print homology'Op /-
/-- Given `f, g` with `f ≫ g = 0`, the homology of `g.op, f.op` is the opposite of the homology of
`f, g`. -/
def homology'Op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology' g.op f.op (by rw [← op_comp, w, op_zero]) ≅ Opposite.op (homology' f g w) :=
  cokernelIsoOfEq (imageToKernel_op _ _ w) ≪≫
    cokernelEpiComp _ _ ≪≫
      cokernelCompIsIso _ _ ≪≫
        cokernelOpOp _ ≪≫
          (homology'IsoKernelDesc _ _ _ ≪≫
              kernelIsoOfEq
                  (by ext <;> simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]) ≪≫
                kernelCompMono _ (image.ι g)).op
#align homology_op homology'Op
-/

#print homology'Unop /-
/-- Given morphisms `f, g` in `Vᵒᵖ` with `f ≫ g = 0`, the homology of `g.unop, f.unop` is the
opposite of the homology of `f, g`. -/
def homology'Unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology' g.unop f.unop (by rw [← unop_comp, w, unop_zero]) ≅ Opposite.unop (homology' f g w) :=
  cokernelIsoOfEq (imageToKernel_unop _ _ w) ≪≫
    cokernelEpiComp _ _ ≪≫
      cokernelCompIsIso _ _ ≪≫
        cokernelUnopUnop _ ≪≫
          (homology'IsoKernelDesc _ _ _ ≪≫
              kernelIsoOfEq
                  (by ext <;> simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]) ≪≫
                kernelCompMono _ (image.ι g)).unop
#align homology_unop homology'Unop
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
  d_comp_d' := by intros; rw [← op_comp, X.d_comp_d, op_zero]
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
  d_comp_d' := by intros; rw [← op_comp, X.d_comp_d, op_zero]
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
  d_comp_d' := by intros; rw [← unop_comp, X.d_comp_d, unop_zero]
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
  d_comp_d' := by intros; rw [← unop_comp, X.d_comp_d, unop_zero]
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
        simpa only [iso.refl_hom, category.id_comp, category.comp_id])
    (by
      intro X Y f
      ext
      simpa only [Quiver.Hom.unop_op, Quiver.Hom.op_unop, functor.comp_map, functor.id_map,
        iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f])
#align homological_complex.op_counit_iso HomologicalComplex.opCounitIso
-/

#print HomologicalComplex.opEquivalence /-
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
-/

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
        simpa only [iso.refl_hom, category.id_comp, category.comp_id])
    (by
      intro X Y f
      ext
      simpa only [Quiver.Hom.unop_op, Quiver.Hom.op_unop, functor.comp_map, functor.id_map,
        iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f])
#align homological_complex.unop_counit_iso HomologicalComplex.unopCounitIso
-/

#print HomologicalComplex.unopEquivalence /-
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
-/

variable {V c}

#print HomologicalComplex.opFunctor_additive /-
instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where
#align homological_complex.op_functor_additive HomologicalComplex.opFunctor_additive
-/

#print HomologicalComplex.unopFunctor_additive /-
instance unopFunctor_additive : (@unopFunctor ι V _ c _).Additive where
#align homological_complex.unop_functor_additive HomologicalComplex.unopFunctor_additive
-/

end

variable [Abelian V] (C : HomologicalComplex V c) (i : ι)

#print HomologicalComplex.homology'OpDef /-
/-- Auxilliary tautological definition for `homology_op`. -/
def homology'OpDef :
    C.op.homology' i ≅
      homology' (C.dFrom i).op (C.dTo i).op (by rw [← op_comp, C.d_to_comp_d_from i, op_zero]) :=
  Iso.refl _
#align homological_complex.homology_op_def HomologicalComplex.homology'OpDef
-/

#print HomologicalComplex.homology'Op /-
/-- Given a complex `C` of objects in `V`, the `i`th homology of its 'opposite' complex (with
objects in `Vᵒᵖ`) is the opposite of the `i`th homology of `C`. -/
def homology'Op : C.op.homology' i ≅ Opposite.op (C.homology' i) :=
  homology'OpDef _ _ ≪≫ homology'Op _ _ _
#align homological_complex.homology_op HomologicalComplex.homology'Op
-/

#print HomologicalComplex.homology'UnopDef /-
/-- Auxilliary tautological definition for `homology_unop`. -/
def homology'UnopDef (C : HomologicalComplex Vᵒᵖ c) :
    C.unop.homology' i ≅
      homology' (C.dFrom i).unop (C.dTo i).unop
        (by rw [← unop_comp, C.d_to_comp_d_from i, unop_zero]) :=
  Iso.refl _
#align homological_complex.homology_unop_def HomologicalComplex.homology'UnopDef
-/

#print HomologicalComplex.homology'Unop /-
/-- Given a complex `C` of objects in `Vᵒᵖ`, the `i`th homology of its 'opposite' complex (with
objects in `V`) is the opposite of the `i`th homology of `C`. -/
def homology'Unop (C : HomologicalComplex Vᵒᵖ c) :
    C.unop.homology' i ≅ Opposite.unop (C.homology' i) :=
  homology'UnopDef _ _ ≪≫ homology'Unop _ _ _
#align homological_complex.homology_unop HomologicalComplex.homology'Unop
-/

end HomologicalComplex

