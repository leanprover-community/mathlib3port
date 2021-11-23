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


noncomputable theory

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable{C : Type u}[category.{v} C]

section 

variable[has_zero_morphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class simple(X : C) : Prop where 
  mono_is_iso_iff_nonzero : ∀ {Y : C} f : Y ⟶ X [mono f], is_iso f ↔ f ≠ 0

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
theorem is_iso_of_mono_of_nonzero {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : f ≠ 0) : is_iso f :=
  (simple.mono_is_iso_iff_nonzero f).mpr w

-- error in CategoryTheory.Simple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem kernel_zero_of_nonzero_from_simple
{X Y : C}
[simple X]
{f : «expr ⟶ »(X, Y)}
[has_kernel f]
(w : «expr ≠ »(f, 0)) : «expr = »(kernel.ι f, 0) :=
begin
  classical,
  by_contradiction [ident h],
  haveI [] [] [":=", expr is_iso_of_mono_of_nonzero h],
  exact [expr w (eq_zero_of_epi_kernel f)]
end

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

instance  (X : C) [simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 0 (id_nonzero X)

section 

variable[has_zero_object C]

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

variable[abelian C]

-- error in CategoryTheory.Simple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
theorem simple_of_cosimple
(X : C)
(h : ∀ {Z : C} (f : «expr ⟶ »(X, Z)) [epi f], «expr ↔ »(is_iso f, «expr ≠ »(f, 0))) : simple X :=
⟨λ Y f I, begin
   classical,
   fsplit,
   { introsI [],
     have [ident hx] [] [":=", expr cokernel.π_of_epi f],
     by_contradiction [ident h],
     substI [expr h],
     exact [expr (h _).mp (cokernel.π_of_zero _ _) hx] },
   { intro [ident hf],
     suffices [] [":", expr epi f],
     { resetI,
       apply [expr abelian.is_iso_of_mono_of_epi] },
     apply [expr preadditive.epi_of_cokernel_zero],
     by_contradiction [ident h'],
     exact [expr cokernel_not_iso_of_nonzero hf ((h _).mpr h')] }
 end⟩

-- error in CategoryTheory.Simple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A nonzero epimorphism from a simple object is an isomorphism. -/
theorem is_iso_of_epi_of_nonzero {X Y : C} [simple X] {f : «expr ⟶ »(X, Y)} [epi f] (w : «expr ≠ »(f, 0)) : is_iso f :=
begin
  haveI [] [":", expr mono f] [":=", expr preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))],
  exact [expr abelian.is_iso_of_mono_of_epi f]
end

-- error in CategoryTheory.Simple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cokernel_zero_of_nonzero_to_simple
{X Y : C}
[simple Y]
{f : «expr ⟶ »(X, Y)}
[has_cokernel f]
(w : «expr ≠ »(f, 0)) : «expr = »(cokernel.π f, 0) :=
begin
  classical,
  by_contradiction [ident h],
  haveI [] [] [":=", expr is_iso_of_epi_of_nonzero h],
  exact [expr w (eq_zero_of_mono_cokernel f)]
end

theorem epi_from_simple_zero_of_not_iso {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : is_iso f → False) : f = 0 :=
  by 
    classical 
    byContra h 
    apply w 
    exact is_iso_of_epi_of_nonzero h

end Abelian

end CategoryTheory

