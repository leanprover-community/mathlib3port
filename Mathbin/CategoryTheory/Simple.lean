/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module category_theory.simple
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Subobject.Lattice
import Mathbin.Order.Atoms

/-!
# Simple objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop` valued typeclass `simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

#print CategoryTheory.Simple /-
/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class Simple (X : C) : Prop where
  mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0
#align category_theory.simple CategoryTheory.Simple
-/

#print CategoryTheory.isIso_of_mono_of_nonzero /-
/-- A nonzero monomorphism to a simple object is an isomorphism. -/
theorem isIso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f ≠ 0) : IsIso f :=
  (Simple.mono_isIso_iff_nonzero f).mpr w
#align category_theory.is_iso_of_mono_of_nonzero CategoryTheory.isIso_of_mono_of_nonzero
-/

#print CategoryTheory.Simple.of_iso /-
theorem Simple.of_iso {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X :=
  {
    mono_isIso_iff_nonzero := fun Z f m => by
      skip
      haveI : mono (f ≫ i.hom) := mono_comp _ _
      constructor
      · intro h w
        have j : is_iso (f ≫ i.hom)
        infer_instance
        rw [simple.mono_is_iso_iff_nonzero] at j
        subst w
        simpa using j
      · intro h
        have j : is_iso (f ≫ i.hom) :=
          by
          apply is_iso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← category.comp_id f, ← i.hom_inv_id, ← category.assoc]
        infer_instance }
#align category_theory.simple.of_iso CategoryTheory.Simple.of_iso
-/

#print CategoryTheory.Simple.iff_of_iso /-
theorem Simple.iff_of_iso {X Y : C} (i : X ≅ Y) : Simple X ↔ Simple Y :=
  ⟨fun h => simple.of_iso i.symm, fun h => simple.of_iso i⟩
#align category_theory.simple.iff_of_iso CategoryTheory.Simple.iff_of_iso
-/

#print CategoryTheory.kernel_zero_of_nonzero_from_simple /-
theorem kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f]
    (w : f ≠ 0) : kernel.ι f = 0 := by
  classical
    by_contra
    haveI := is_iso_of_mono_of_nonzero h
    exact w (eq_zero_of_epi_kernel f)
#align category_theory.kernel_zero_of_nonzero_from_simple CategoryTheory.kernel_zero_of_nonzero_from_simple
-/

#print CategoryTheory.epi_of_nonzero_to_simple /-
-- See also `mono_of_nonzero_from_simple`, which requires `preadditive C`.
/-- A nonzero morphism `f` to a simple object is an epimorphism
(assuming `f` has an image, and `C` has equalizers).
-/
theorem epi_of_nonzero_to_simple [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y} [HasImage f]
    (w : f ≠ 0) : Epi f := by
  rw [← image.fac f]
  haveI : is_iso (image.ι f) := is_iso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp
#align category_theory.epi_of_nonzero_to_simple CategoryTheory.epi_of_nonzero_to_simple
-/

#print CategoryTheory.mono_to_simple_zero_of_not_iso /-
theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f]
    (w : IsIso f → False) : f = 0 := by
  classical
    by_contra
    exact w (is_iso_of_mono_of_nonzero h)
#align category_theory.mono_to_simple_zero_of_not_iso CategoryTheory.mono_to_simple_zero_of_not_iso
-/

#print CategoryTheory.id_nonzero /-
theorem id_nonzero (X : C) [Simple.{v} X] : 𝟙 X ≠ 0 :=
  (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
#align category_theory.id_nonzero CategoryTheory.id_nonzero
-/

instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 0 (id_nonzero X)

section

#print CategoryTheory.Simple.not_isZero /-
theorem Simple.not_isZero (X : C) [Simple X] : ¬IsZero X := by
  simpa [limits.is_zero.iff_id_eq_zero] using id_nonzero X
#align category_theory.simple.not_is_zero CategoryTheory.Simple.not_isZero
-/

variable [HasZeroObject C]

open ZeroObject

variable (C)

#print CategoryTheory.zero_not_simple /-
/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by tidy⟩⟩ rfl
#align category_theory.zero_not_simple CategoryTheory.zero_not_simple
-/

end

end

-- We next make the dual arguments, but for this we must be in an abelian category.
section Abelian

variable [Abelian C]

#print CategoryTheory.simple_of_cosimple /-
/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
theorem simple_of_cosimple (X : C) (h : ∀ {Z : C} (f : X ⟶ Z) [Epi f], IsIso f ↔ f ≠ 0) :
    Simple X :=
  ⟨fun Y f I => by
    classical
      fconstructor
      · intros
        have hx := cokernel.π_of_epi f
        by_contra
        subst h
        exact (h _).mp (cokernel.π_of_zero _ _) hx
      · intro hf
        suffices epi f by exact is_iso_of_mono_of_epi _
        apply preadditive.epi_of_cokernel_zero
        by_contra h'
        exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩
#align category_theory.simple_of_cosimple CategoryTheory.simple_of_cosimple
-/

#print CategoryTheory.isIso_of_epi_of_nonzero /-
/-- A nonzero epimorphism from a simple object is an isomorphism. -/
theorem isIso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f ≠ 0) : IsIso f :=
  haveI-- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
   : mono f :=
    preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  is_iso_of_mono_of_epi f
#align category_theory.is_iso_of_epi_of_nonzero CategoryTheory.isIso_of_epi_of_nonzero
-/

#print CategoryTheory.cokernel_zero_of_nonzero_to_simple /-
theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
    cokernel.π f = 0 := by
  classical
    by_contra h
    haveI := is_iso_of_epi_of_nonzero h
    exact w (eq_zero_of_mono_cokernel f)
#align category_theory.cokernel_zero_of_nonzero_to_simple CategoryTheory.cokernel_zero_of_nonzero_to_simple
-/

#print CategoryTheory.epi_from_simple_zero_of_not_iso /-
theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f]
    (w : IsIso f → False) : f = 0 := by
  classical
    by_contra
    exact w (is_iso_of_epi_of_nonzero h)
#align category_theory.epi_from_simple_zero_of_not_iso CategoryTheory.epi_from_simple_zero_of_not_iso
-/

end Abelian

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

#print CategoryTheory.Biprod.isIso_inl_iff_isZero /-
-- There are another three potential variations of this lemma,
-- but as any one suffices to prove `indecomposable_of_simple` we will not give them all.
theorem Biprod.isIso_inl_iff_isZero (X Y : C) : IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y :=
  by
  rw [biprod.is_iso_inl_iff_id_eq_fst_comp_inl, ← biprod.total, add_right_eq_self]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← is_zero.iff_is_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [is_zero.iff_is_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h, zero_comp]
#align category_theory.biprod.is_iso_inl_iff_is_zero CategoryTheory.Biprod.isIso_inl_iff_isZero
-/

#print CategoryTheory.indecomposable_of_simple /-
/-- Any simple object in a preadditive category is indecomposable. -/
theorem indecomposable_of_simple (X : C) [Simple X] : Indecomposable X :=
  ⟨Simple.not_isZero X, fun Y Z i =>
    by
    refine' or_iff_not_imp_left.mpr fun h => _
    rw [is_zero.iff_is_split_mono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl ≠ 0 at h
    rw [← simple.mono_is_iso_iff_nonzero biprod.inl] at h
    · rwa [biprod.is_iso_inl_iff_is_zero] at h
    · exact simple.of_iso i.symm
    · infer_instance⟩
#align category_theory.indecomposable_of_simple CategoryTheory.indecomposable_of_simple
-/

end Indecomposable

section Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

open Subobject

instance {X : C} [Simple X] : Nontrivial (Subobject X) :=
  nontrivial_of_not_isZero (Simple.not_isZero X)

instance {X : C} [Simple X] : IsSimpleOrder (Subobject X)
    where eq_bot_or_eq_top :=
    by
    rintro ⟨⟨⟨Y : C, ⟨⟨⟩⟩, f : Y ⟶ X⟩, m : mono f⟩⟩; skip
    change mk f = ⊥ ∨ mk f = ⊤
    by_cases h : f = 0
    · exact Or.inl (mk_eq_bot_iff_zero.mpr h)
    · refine' Or.inr ((is_iso_iff_mk_eq_top _).mp ((simple.mono_is_iso_iff_nonzero f).mpr h))

#print CategoryTheory.simple_of_isSimpleOrder_subobject /-
/-- If `X` has subobject lattice `{⊥, ⊤}`, then `X` is simple. -/
theorem simple_of_isSimpleOrder_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X :=
  by
  constructor; intros ; constructor
  · intro i
    rw [subobject.is_iso_iff_mk_eq_top] at i
    intro w
    rw [← subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (subobject.mk f) with (h | h)
    · rw [subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (subobject.is_iso_iff_mk_eq_top _).mpr h
#align category_theory.simple_of_is_simple_order_subobject CategoryTheory.simple_of_isSimpleOrder_subobject
-/

#print CategoryTheory.simple_iff_subobject_isSimpleOrder /-
/-- `X` is simple iff it has subobject lattice `{⊥, ⊤}`. -/
theorem simple_iff_subobject_isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X) :=
  ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_is_simple_order_subobject X⟩
#align category_theory.simple_iff_subobject_is_simple_order CategoryTheory.simple_iff_subobject_isSimpleOrder
-/

/- warning: category_theory.subobject_simple_iff_is_atom -> CategoryTheory.subobject_simple_iff_isAtom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u2} C _inst_1] {X : C} (Y : CategoryTheory.Subobject.{u1, u2} C _inst_1 X), Iff (CategoryTheory.Simple.{u1, u2} C _inst_1 _inst_2 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) C (CategoryTheory.Subobject.hasCoe.{u1, u2} C _inst_1 X)))) Y)) (IsAtom.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.Subobject.partialOrder.{u2, u1} C _inst_1 X)) (CategoryTheory.Subobject.orderBot.{u1, u2} C _inst_1 (CategoryTheory.Limits.HasZeroObject.hasInitial.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.HasZeroObject.initialMonoClass.{u1, u2} C _inst_1 _inst_3) X) Y)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u2} C _inst_1] {X : C} (Y : CategoryTheory.Subobject.{u1, u2} C _inst_1 X), Iff (CategoryTheory.Simple.{u1, u2} C _inst_1 _inst_2 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.instPartialOrderSubobject.{u1, u2} C _inst_1 X))))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.instPartialOrderSubobject.{u1, u2} C _inst_1 X))) C _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} C _inst_1 X)) Y)) (IsAtom.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.instPartialOrderSubobject.{u1, u2} C _inst_1 X)) (CategoryTheory.Subobject.orderBot.{u1, u2} C _inst_1 (CategoryTheory.Limits.HasZeroObject.hasInitial.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.HasZeroObject.initialMonoClass.{u1, u2} C _inst_1 _inst_3) X) Y)
Case conversion may be inaccurate. Consider using '#align category_theory.subobject_simple_iff_is_atom CategoryTheory.subobject_simple_iff_isAtomₓ'. -/
/-- A subobject is simple iff it is an atom in the subobject lattice. -/
theorem subobject_simple_iff_isAtom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y :=
  (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)
#align category_theory.subobject_simple_iff_is_atom CategoryTheory.subobject_simple_iff_isAtom

end Subobject

end CategoryTheory

