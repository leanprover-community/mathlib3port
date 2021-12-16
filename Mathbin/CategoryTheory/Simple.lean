import Mathbin.CategoryTheory.Limits.Shapes.Zero 
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

variable {C : Type u} [category.{v} C]

section 

variable [has_zero_morphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class simple (X : C) : Prop where 
  mono_is_iso_iff_nonzero : ∀ {Y : C} f : Y ⟶ X [mono f], is_iso f ↔ f ≠ 0

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
theorem is_iso_of_mono_of_nonzero {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : f ≠ 0) : is_iso f :=
  (simple.mono_is_iso_iff_nonzero f).mpr w

theorem kernel_zero_of_nonzero_from_simple {X Y : C} [simple X] {f : X ⟶ Y} [has_kernel f] (w : f ≠ 0) :
  kernel.ι f = 0 :=
  by 
    classical 
    byContra h 
    have  := is_iso_of_mono_of_nonzero h 
    exact w (eq_zero_of_epi_kernel f)

theorem mono_to_simple_zero_of_not_iso {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : is_iso f → False) : f = 0 :=
  by 
    classical 
    byContra h 
    apply w 
    exact is_iso_of_mono_of_nonzero h

theorem id_nonzero (X : C) [simple.{v} X] : 𝟙 X ≠ 0 :=
  (simple.mono_is_iso_iff_nonzero (𝟙 X)).mp
    (by 
      infer_instance)

instance (X : C) [simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 0 (id_nonzero X)

section 

variable [has_zero_object C]

open_locale ZeroObject

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
theorem zero_not_simple [simple (0 : C)] : False :=
  (simple.mono_is_iso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp
    ⟨⟨0,
        by 
          tidy⟩⟩
    rfl

end 

end 

section Abelian

variable [abelian C]

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
theorem simple_of_cosimple (X : C) (h : ∀ {Z : C} f : X ⟶ Z [epi f], is_iso f ↔ f ≠ 0) : simple X :=
  ⟨fun Y f I =>
      by 
        classical 
        fconstructor
        ·
          intros 
          have hx := cokernel.π_of_epi f 
          byContra h 
          subst h 
          exact (h _).mp (cokernel.π_of_zero _ _) hx
        ·
          intro hf 
          suffices  : epi f
          ·
            skip 
            apply abelian.is_iso_of_mono_of_epi 
          apply preadditive.epi_of_cokernel_zero 
          byContra h' 
          exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
theorem is_iso_of_epi_of_nonzero {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : f ≠ 0) : is_iso f :=
  by 
    have  : mono f := preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
    exact abelian.is_iso_of_mono_of_epi f

theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [simple Y] {f : X ⟶ Y} [has_cokernel f] (w : f ≠ 0) :
  cokernel.π f = 0 :=
  by 
    classical 
    byContra h 
    have  := is_iso_of_epi_of_nonzero h 
    exact w (eq_zero_of_mono_cokernel f)

theorem epi_from_simple_zero_of_not_iso {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : is_iso f → False) : f = 0 :=
  by 
    classical 
    byContra h 
    apply w 
    exact is_iso_of_epi_of_nonzero h

end Abelian

end CategoryTheory

