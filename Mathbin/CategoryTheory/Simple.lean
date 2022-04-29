/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Abelian.Basic

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop` valued typeclass `simple X`.

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.
-/


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class Simple (X : C) : Prop where
  mono_is_iso_iff_nonzero : ∀ {Y : C} f : Y ⟶ X [Mono f], IsIso f ↔ f ≠ 0

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
theorem is_iso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f ≠ 0) : IsIso f :=
  (Simple.mono_is_iso_iff_nonzero f).mpr w

theorem kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f] (w : f ≠ 0) :
    kernel.ι f = 0 := by
  classical
  by_contra
  have := is_iso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : IsIso f → False) : f = 0 := by
  classical
  by_contra
  exact w (is_iso_of_mono_of_nonzero h)

theorem id_nonzero (X : C) [Simple.{v} X] : 𝟙 X ≠ 0 :=
  (Simple.mono_is_iso_iff_nonzero (𝟙 X)).mp
    (by
      infer_instance)

instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 0 (id_nonzero X)

section

variable [HasZeroObject C]

open ZeroObject

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_is_iso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp
    ⟨⟨0, by
        tidy⟩⟩
    rfl

end

end

-- We next make the dual arguments, but for this we must be in an abelian category.
section Abelian

variable [Abelian C]

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
theorem simple_of_cosimple (X : C) (h : ∀ {Z : C} f : X ⟶ Z [Epi f], IsIso f ↔ f ≠ 0) : Simple X :=
  ⟨fun Y f I => by
    classical
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra
      subst h
      exact (h _).mp (cokernel.π_of_zero _ _) hx
      
    · intro hf
      suffices epi f by
        exact is_iso_of_mono_of_epi _
      apply preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')
      ⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
theorem is_iso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f ≠ 0) : IsIso f :=
  have-- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
   : mono f := preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  is_iso_of_mono_of_epi f

theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : cokernel.π f = 0 := by
  classical
  by_contra h
  have := is_iso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)

theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : IsIso f → False) : f = 0 := by
  classical
  by_contra
  exact w (is_iso_of_epi_of_nonzero h)

end Abelian

end CategoryTheory

