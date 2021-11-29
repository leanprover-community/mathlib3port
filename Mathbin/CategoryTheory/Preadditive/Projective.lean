import Mathbin.Algebra.Homology.Exact 
import Mathbin.CategoryTheory.Types 
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class projective (P : C) : Prop where 
  Factors : ∀ {E X : C} f : P ⟶ X e : E ⟶ X [epi e], ∃ f', f' ≫ e = f

section 

/--
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_inhabited_instance]
structure projective_presentation (X : C) where 
  P : C 
  Projective : projective P :=  by 
  runTac 
    tactic.apply_instance 
  f : P ⟶ X 
  Epi : epi f :=  by 
  runTac 
    tactic.apply_instance

variable (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop where 
  presentation : ∀ X : C, Nonempty (projective_presentation X)

end 

namespace Projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factor_thru {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : P ⟶ E :=
  (projective.factors f e).some

@[simp]
theorem factor_thru_comp {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : factor_thru f e ≫ e = f :=
  (projective.factors f e).some_spec

section 

open_locale ZeroObject

instance zero_projective [has_zero_object C] [has_zero_morphisms C] : projective (0 : C) :=
  { Factors :=
      fun E X f e epi =>
        by 
          use 0 
          ext }

end 

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
  by 
    fsplit 
    intros E X f e e_epi 
    obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e 
    exact
      ⟨i.inv ≫ f',
        by 
          simp [hf']⟩

theorem iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : projective X :=
  { Factors :=
      fun E X' f e epi =>
        ⟨fun x => ((epi_iff_surjective _).mp epi (f x)).some,
          by 
            ext x 
            exact ((epi_iff_surjective _).mp epi (f x)).some_spec⟩ }

instance Type.enough_projectives : enough_projectives (Type u) :=
  { presentation := fun X => ⟨{ P := X, f := 𝟙 X }⟩ }

instance {P Q : C} [has_binary_coproduct P Q] [projective P] [projective Q] : projective (P ⨿ Q) :=
  { Factors :=
      fun E X' f e epi =>
        by 
          exact
            ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e),
              by 
                tidy⟩ }

instance {β : Type v} (g : β → C) [has_coproduct g] [∀ b, projective (g b)] : projective (∐ g) :=
  { Factors :=
      fun E X' f e epi =>
        by 
          exact
            ⟨sigma.desc fun b => factor_thru (sigma.ι g b ≫ f) e,
              by 
                tidy⟩ }

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q] [projective P] [projective Q] :
  projective (P ⊞ Q) :=
  { Factors :=
      fun E X' f e epi =>
        by 
          exact
            ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e),
              by 
                tidy⟩ }

instance {β : Type v} [DecidableEq β] (g : β → C) [has_zero_morphisms C] [has_biproduct g] [∀ b, projective (g b)] :
  projective (⨁ g) :=
  { Factors :=
      fun E X' f e epi =>
        by 
          exact
            ⟨biproduct.desc fun b => factor_thru (biproduct.ι g b ≫ f) e,
              by 
                tidy⟩ }

section EnoughProjectives

variable [enough_projectives C]

/--
`projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (enough_projectives.presentation X).some.P

instance projective_over (X : C) : projective (over X) :=
  (enough_projectives.presentation X).some.Projective

/--
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (enough_projectives.presentation X).some.f

instance π_epi (X : C) : epi (π X) :=
  (enough_projectives.presentation X).some.Epi

section 

variable [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

-- error in CategoryTheory.Preadditive.Projective: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler projective
/--
When `C` has enough projectives, the object `projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/ @[derive #[expr projective]] def syzygies : C :=
over (kernel f)

/--
When `C` has enough projectives,
`projective.d f : projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbrev d : syzygies f ⟶ X :=
  π (kernel f) ≫ kernel.ι f

end 

end EnoughProjectives

end Projective

open Projective

section 

variable [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
Given a projective object `P` mapping via `h` into
the middle object `R` of a pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def exact.lift {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S) [exact f g] (w : h ≫ g = 0) : P ⟶ Q :=
  factor_thru
    (factor_thru (factor_thru_kernel_subobject g h w)
      (imageToKernel f g
        (by 
          simp )))
    (factor_thru_image_subobject f)

@[simp]
theorem exact.lift_comp {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S) [exact f g] (w : h ≫ g = 0) :
  exact.lift h f g w ≫ f = h :=
  by 
    simp [exact.lift]
    convLHS => congr skip rw [←image_subobject_arrow_comp f]
    rw [←category.assoc, factor_thru_comp, ←image_to_kernel_arrow, ←category.assoc,
      CategoryTheory.Projective.factor_thru_comp, factor_thru_kernel_subobject_comp_arrow]

end 

end CategoryTheory

