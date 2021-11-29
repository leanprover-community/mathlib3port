import Mathbin.CategoryTheory.Subobject.Basic 
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Factoring through subobjects

The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.

-/


universe v₁ v₂ u₁ u₂

noncomputable theory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

/-- When `f : X ⟶ Y` and `P : mono_over Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : mono_over Y) (f : X ⟶ Y) : Prop :=
  ∃ g : X ⟶ (P : C), g ≫ P.arrow = f

theorem factors_congr {X : C} {f g : mono_over X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) : f.factors h ↔ g.factors h :=
  ⟨fun ⟨u, hu⟩ =>
      ⟨u ≫ ((mono_over.forget _).map e.hom).left,
        by 
          simp [hu]⟩,
    fun ⟨u, hu⟩ =>
      ⟨u ≫ ((mono_over.forget _).map e.inv).left,
        by 
          simp [hu]⟩⟩

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : mono_over Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : mono_over Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ (P : C) :=
  Classical.some h

end MonoOver

namespace Subobject

/-- When `f : X ⟶ Y` and `P : subobject Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : subobject Y) (f : X ⟶ Y) : Prop :=
  Quotientₓ.liftOn' P (fun P => P.factors f)
    (by 
      rintro P Q ⟨h⟩
      apply propext 
      split 
      ·
        rintro ⟨i, w⟩
        exact
          ⟨i ≫ h.hom.left,
            by 
              erw [category.assoc, over.w h.hom, w]⟩
      ·
        rintro ⟨i, w⟩
        exact
          ⟨i ≫ h.inv.left,
            by 
              erw [category.assoc, over.w h.inv, w]⟩)

@[simp]
theorem mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [mono f] (g : Z ⟶ X) :
  (subobject.mk f).Factors g ↔ (mono_over.mk' f).Factors g :=
  Iff.rfl

theorem factors_iff {X Y : C} (P : subobject Y) (f : X ⟶ Y) : P.factors f ↔ (representative.obj P).Factors f :=
  Quot.induction_on P$ fun a => mono_over.factors_congr _ (representative_iso _).symm

theorem factors_self {X : C} (P : subobject X) : P.factors P.arrow :=
  (factors_iff _ _).mpr
    ⟨𝟙 P,
      by 
        simp ⟩

theorem factors_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) : P.factors (f ≫ P.arrow) :=
  (factors_iff _ _).mpr ⟨f, rfl⟩

theorem factors_of_factors_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z} (h : P.factors g) :
  P.factors (f ≫ g) :=
  by 
    revert P 
    refine' Quotientₓ.ind' _ 
    intro P 
    rintro ⟨g, rfl⟩
    exact
      ⟨f ≫ g,
        by 
          simp ⟩

theorem factors_zero [has_zero_morphisms C] {X Y : C} {P : subobject Y} : P.factors (0 : X ⟶ Y) :=
  (factors_iff _ _).mpr
    ⟨0,
      by 
        simp ⟩

theorem factors_of_le {Y Z : C} {P Q : subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) : P.factors f → Q.factors f :=
  by 
    simp only [factors_iff]
    exact
      fun ⟨u, hu⟩ =>
        ⟨u ≫ of_le _ _ h,
          by 
            simp [←hu]⟩

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : subobject Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P :=
  Classical.some ((factors_iff _ _).mp h)

@[simp, reassoc]
theorem factor_thru_arrow {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) : P.factor_thru f h ≫ P.arrow = f :=
  Classical.some_spec ((factors_iff _ _).mp h)

@[simp]
theorem factor_thru_self {X : C} (P : subobject X) h : P.factor_thru P.arrow h = 𝟙 P :=
  by 
    ext 
    simp 

@[simp]
theorem factor_thru_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) h : P.factor_thru (f ≫ P.arrow) h = f :=
  by 
    ext 
    simp 

@[simp]
theorem factor_thru_eq_zero [has_zero_morphisms C] {X Y : C} {P : subobject Y} {f : X ⟶ Y} {h : factors P f} :
  P.factor_thru f h = 0 ↔ f = 0 :=
  by 
    fsplit
    ·
      intro w 
      replace w := w =≫ P.arrow 
      simpa using w
    ·
      rintro rfl 
      ext 
      simp 

theorem factor_thru_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.factors g) :
  f ≫ P.factor_thru g h = P.factor_thru (f ≫ g) (factors_of_factors_right f h) :=
  by 
    apply (cancel_mono P.arrow).mp 
    simp 

@[simp]
theorem factor_thru_zero [has_zero_morphisms C] {X Y : C} {P : subobject Y} (h : P.factors (0 : X ⟶ Y)) :
  P.factor_thru 0 h = 0 :=
  by 
    simp 

theorem factor_thru_of_le {Y Z : C} {P Q : subobject Y} {f : Z ⟶ Y} (h : P ≤ Q) (w : P.factors f) :
  Q.factor_thru f (factors_of_le f h w) = P.factor_thru f w ≫ of_le P Q h :=
  by 
    ext 
    simp 

section Preadditive

variable [preadditive C]

theorem factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (wf : P.factors f) (wg : P.factors g) : P.factors (f+g) :=
  (factors_iff _ _).mpr
    ⟨P.factor_thru f wf+P.factor_thru g wg,
      by 
        simp ⟩

theorem factor_thru_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (w : P.factors (f+g)) (wf : P.factors f)
  (wg : P.factors g) : P.factor_thru (f+g) w = P.factor_thru f wf+P.factor_thru g wg :=
  by 
    ext 
    simp 

theorem factors_left_of_factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (w : P.factors (f+g)) (wg : P.factors g) :
  P.factors f :=
  (factors_iff _ _).mpr
    ⟨P.factor_thru (f+g) w - P.factor_thru g wg,
      by 
        simp ⟩

@[simp]
theorem factor_thru_add_sub_factor_thru_right {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (w : P.factors (f+g))
  (wg : P.factors g) :
  P.factor_thru (f+g) w - P.factor_thru g wg = P.factor_thru f (factors_left_of_factors_add f g w wg) :=
  by 
    ext 
    simp 

theorem factors_right_of_factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (w : P.factors (f+g))
  (wf : P.factors f) : P.factors g :=
  (factors_iff _ _).mpr
    ⟨P.factor_thru (f+g) w - P.factor_thru f wf,
      by 
        simp ⟩

@[simp]
theorem factor_thru_add_sub_factor_thru_left {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (w : P.factors (f+g))
  (wf : P.factors f) :
  P.factor_thru (f+g) w - P.factor_thru f wf = P.factor_thru g (factors_right_of_factors_add f g w wf) :=
  by 
    ext 
    simp 

end Preadditive

end Subobject

end CategoryTheory

