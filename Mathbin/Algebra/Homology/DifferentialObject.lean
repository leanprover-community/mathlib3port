import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/


open CategoryTheory

open CategoryTheory.Limits

open_locale Classical

noncomputable section

namespace HomologicalComplex

variable {β : Type _} [AddCommGroupₓ β] {b : β}

variable {V : Type _} [category V] [has_zero_morphisms V]

/-- Since `eq_to_hom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
abbrev _root_.category_theory.differential_object.X_eq_to_hom (X : differential_object (graded_object_with_shift b V))
    {i j : β} (h : i = j) : X.X i ⟶ X.X j :=
  eq_to_hom (congr_argₓ X.X h)

@[simp]
theorem _root_.category_theory.differential_object.X_eq_to_hom_refl
    (X : differential_object (graded_object_with_shift b V)) (i : β) : X.X_eq_to_hom (refl i) = 𝟙 _ :=
  rfl

@[simp, reassoc]
theorem eq_to_hom_d (X : differential_object (graded_object_with_shift b V)) {x y : β} (h : x = y) :
    X.X_eq_to_hom h ≫ X.d y =
      X.d x ≫
        X.X_eq_to_hom
          (by
            cases h
            rfl) :=
  by
  cases h
  dsimp
  simp

@[simp, reassoc]
theorem d_eq_to_hom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eq_to_hom (congr_argₓ X.X h) = X.d x z := by
  cases h
  simp

@[simp, reassoc]
theorem eq_to_hom_f {X Y : differential_object (graded_object_with_shift b V)} (f : X ⟶ Y) {x y : β} (h : x = y) :
    X.X_eq_to_hom h ≫ f.f y = f.f x ≫ Y.X_eq_to_hom h := by
  cases h
  simp

variable (b V)

attribute [local reducible] graded_object.has_shift

/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgo_to_homological_complex :
    differential_object (graded_object_with_shift b V) ⥤ HomologicalComplex V (ComplexShape.up' b) where
  obj := fun X =>
    { x := fun i => X.X i,
      d := fun i j =>
        if h : i + b = j then
          X.d i ≫
            X.X_eq_to_hom
              (show i + (1 : ℤ) • b = j by
                simp [h])
        else 0,
      shape' := fun i j w => by
        dsimp  at w
        convert dif_neg w,
      d_comp_d' := fun i j k hij hjk => by
        dsimp  at hij hjk
        substs hij hjk
        have : X.d i ≫ X.d _ = _ := (congr_funₓ X.d_squared i : _)
        reassoc! this
        simp [this] }
  map := fun X Y f =>
    { f := f.f,
      comm' := fun i j h => by
        dsimp  at h⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f (i + 1 • b) := (congr_funₓ f.comm i).symm
        reassoc! this
        simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl, this, category.assoc, eq_to_hom_f] }

/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
def homological_complex_to_dgo :
    HomologicalComplex V (ComplexShape.up' b) ⥤ differential_object (graded_object_with_shift b V) where
  obj := fun X =>
    { x := fun i => X.X i, d := fun i => X.d i (i + 1 • b),
      d_squared' := by
        ext i
        dsimp
        simp }
  map := fun X Y f =>
    { f := f.f,
      comm' := by
        ext i
        dsimp
        simp }

/-- The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso :
    𝟭 (differential_object (graded_object_with_shift b V)) ≅
      dgo_to_homological_complex b V ⋙ homological_complex_to_dgo b V :=
  nat_iso.of_components (fun X => { Hom := { f := fun i => 𝟙 (X.X i) }, inv := { f := fun i => 𝟙 (X.X i) } })
    (by
      tidy)

/-- The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_counit_iso :
    homological_complex_to_dgo b V ⋙ dgo_to_homological_complex b V ≅ 𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  nat_iso.of_components
    (fun X =>
      { Hom :=
          { f := fun i => 𝟙 (X.X i),
            comm' := fun i j h => by
              dsimp  at h⊢
              subst h
              delta' homological_complex_to_dgo
              simp },
        inv :=
          { f := fun i => 𝟙 (X.X i),
            comm' := fun i j h => by
              dsimp  at h⊢
              subst h
              delta' homological_complex_to_dgo
              simp } })
    (by
      tidy)

/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgo_equiv_homological_complex :
    differential_object (graded_object_with_shift b V) ≌ HomologicalComplex V (ComplexShape.up' b) where
  Functor := dgo_to_homological_complex b V
  inverse := homological_complex_to_dgo b V
  unitIso := dgo_equiv_homological_complex_unit_iso b V
  counitIso := dgo_equiv_homological_complex_counit_iso b V

end HomologicalComplex

