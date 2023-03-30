/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang, Joël Riou

! This file was ported from Lean 3 source module category_theory.shift.basic
! leanprover-community/mathlib commit 6876fa15e3158ff3e4a4e2af1fb6e1945c6e8803
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Monoidal.End
import Mathbin.CategoryTheory.Monoidal.Discrete

/-!
# Shift

A `shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `has_shift`: A typeclass asserting the existence of a shift functor.
* `shift_equiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shift_comm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[has_shift C A]` is implemented using `monoidal_functor (discrete A) (C ⥤ C)`.
However, the API of monodial functors is used only internally: one should use the API of
shifts functors which includes `shift_functor C a : C ⥤ C` for `a : A`,
`shift_functor_zero C A : shift_functor C (0 : A) ≅ 𝟭 C` and
`shift_functor_add C i j : shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j`
(and its variant `shift_functor_add'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shift_functor_add'_assoc`, `shift_functor_add'_zero_add` and
`shift_functor_add'_add_zero`.

-/


namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type _) [Category.{v} C]

attribute [local instance] endofunctor_monoidal_category

section Defs

variable (A C) [AddMonoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class HasShift (C : Type u) (A : Type _) [Category.{v} C] [AddMonoid A] where
  shift : MonoidalFunctor (Discrete A) (C ⥤ C)
#align category_theory.has_shift CategoryTheory.HasShift

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_nonempty_instance]
structure ShiftMkCore where
  f : A → C ⥤ C
  zero : F 0 ≅ 𝟭 C
  add : ∀ n m : A, F (n + m) ≅ F n ⋙ F m
  assoc_hom_app :
    ∀ (m₁ m₂ m₃ : A) (X : C),
      (add (m₁ + m₂) m₃).Hom.app X ≫ (F m₃).map ((add m₁ m₂).Hom.app X) =
        eqToHom (by rw [add_assoc]) ≫
          (add m₁ (m₂ + m₃)).Hom.app X ≫ (add m₂ m₃).Hom.app ((F m₁).obj X)
  zero_add_hom_app :
    ∀ (n : A) (X : C),
      (add 0 n).Hom.app X = eqToHom (by dsimp <;> rw [zero_add]) ≫ (F n).map (zero.inv.app X)
  add_zero_hom_app :
    ∀ (n : A) (X : C),
      (add n 0).Hom.app X = eqToHom (by dsimp <;> rw [add_zero]) ≫ zero.inv.app ((F n).obj X)
#align category_theory.shift_mk_core CategoryTheory.ShiftMkCore

namespace ShiftMkCore

variable {C A}

attribute [reassoc.1] assoc_hom_app

@[reassoc.1]
theorem assoc_inv_app (h : ShiftMkCore C A) (m₁ m₂ m₃ : A) (X : C) :
    (h.f m₃).map ((h.add m₁ m₂).inv.app X) ≫ (h.add (m₁ + m₂) m₃).inv.app X =
      (h.add m₂ m₃).inv.app ((h.f m₁).obj X) ≫
        (h.add m₁ (m₂ + m₃)).inv.app X ≫ eqToHom (by rw [add_assoc]) :=
  by
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).Hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).Hom.app X)),
    category.assoc, category.assoc, category.assoc, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    iso.inv_hom_id_app, Functor.map_id, h.assoc_hom_app, eq_to_hom_trans_assoc, eq_to_hom_refl,
    category.id_comp, iso.inv_hom_id_app_assoc, iso.inv_hom_id_app]
  rfl
#align category_theory.shift_mk_core.assoc_inv_app CategoryTheory.ShiftMkCore.assoc_inv_app

theorem zero_add_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add 0 n).inv.app X = (h.f n).map (h.zero.Hom.app X) ≫ eqToHom (by dsimp <;> rw [zero_add]) :=
  by
  rw [← cancel_epi ((h.add 0 n).Hom.app X), iso.hom_inv_id_app, h.zero_add_hom_app, category.assoc,
    ← functor.map_comp_assoc, iso.inv_hom_id_app, Functor.map_id, category.id_comp, eq_to_hom_trans,
    eq_to_hom_refl]
#align category_theory.shift_mk_core.zero_add_inv_app CategoryTheory.ShiftMkCore.zero_add_inv_app

theorem add_zero_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add n 0).inv.app X = h.zero.Hom.app ((h.f n).obj X) ≫ eqToHom (by dsimp <;> rw [add_zero]) :=
  by
  rw [← cancel_epi ((h.add n 0).Hom.app X), iso.hom_inv_id_app, h.add_zero_hom_app, category.assoc,
    iso.inv_hom_id_app_assoc, eq_to_hom_trans, eq_to_hom_refl]
#align category_theory.shift_mk_core.add_zero_inv_app CategoryTheory.ShiftMkCore.add_zero_inv_app

end ShiftMkCore

section

attribute [local simp] eq_to_hom_map

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A :=
  ⟨{ Discrete.functor h.f with
      ε := h.zero.inv
      μ := fun m n => (h.add m.as n.as).inv
      μ_natural' := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨Y'⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨⟨⟨rfl⟩⟩⟩
        ext
        dsimp
        simp only [discrete.functor_map_id, category.assoc]
        dsimp
        simp
      associativity' := by
        rintro ⟨m₁⟩ ⟨m₂⟩ ⟨m₃⟩
        ext X
        dsimp
        simp [h.assoc_inv_app_assoc m₁ m₂ m₃ X]
      left_unitality' := by
        rintro ⟨n⟩
        ext X
        dsimp
        simp only [h.zero_add_inv_app, ← functor.map_comp, category.id_comp, eq_to_hom_map,
          eq_to_hom_app, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id,
          iso.inv_hom_id_app]
        erw [Functor.map_id]
      right_unitality' := by
        rintro ⟨n⟩
        ext X
        dsimp
        simpa only [h.add_zero_inv_app, Functor.map_id, category.comp_id, eq_to_hom_map,
          eq_to_hom_app, category.assoc, eq_to_hom_trans, eq_to_hom_refl, iso.inv_hom_id_app] }⟩
#align category_theory.has_shift_mk CategoryTheory.hasShiftMk

end

section

variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shiftMonoidalFunctor : MonoidalFunctor (Discrete A) (C ⥤ C) :=
  HasShift.shift
#align category_theory.shift_monoidal_functor CategoryTheory.shiftMonoidalFunctor

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj ⟨i⟩
#align category_theory.shift_functor CategoryTheory.shiftFunctor

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  ((shiftMonoidalFunctor C A).μIso ⟨i⟩ ⟨j⟩).symm
#align category_theory.shift_functor_add CategoryTheory.shiftFunctorAdd

/-- When `k = i + j`, shifting by `k` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd' (i j k : A) (h : i + j = k) :
    shiftFunctor C k ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j
#align category_theory.shift_functor_add' CategoryTheory.shiftFunctorAdd'

theorem shiftFunctorAdd'_eq_shiftFunctorAdd (i j : A) :
    shiftFunctorAdd' C i j (i + j) rfl = shiftFunctorAdd C i j :=
  by
  ext1
  apply category.id_comp
#align category_theory.shift_functor_add'_eq_shift_functor_add CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd

variable (A)

/-- Shifting by zero is the identity functor. -/
def shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (shiftMonoidalFunctor C A).εIso.symm
#align category_theory.shift_functor_zero CategoryTheory.shiftFunctorZero

end

variable {C A}

theorem ShiftMkCore.shiftFunctor_eq (h : ShiftMkCore C A) (a : A) :
    @shiftFunctor _ _ _ _ (hasShiftMk C A h) a = h.f a :=
  Functor.ext (by tidy) (by tidy)
#align category_theory.shift_mk_core.shift_functor_eq CategoryTheory.ShiftMkCore.shiftFunctor_eq

theorem ShiftMkCore.shiftFunctorZero_eq (h : ShiftMkCore C A) :
    @shiftFunctorZero _ _ _ _ (hasShiftMk C A h) = h.zero :=
  by
  letI := has_shift_mk C A h
  ext1
  suffices (shift_functor_zero C A).inv = h.zero.inv
    by
    rw [← cancel_mono h.zero.inv, h.zero.hom_inv_id, ← this, iso.hom_inv_id]
    rfl
  rfl
#align category_theory.shift_mk_core.shift_functor_zero_eq CategoryTheory.ShiftMkCore.shiftFunctorZero_eq

theorem ShiftMkCore.shiftFunctorAdd_eq (h : ShiftMkCore C A) (a b : A) :
    @shiftFunctorAdd _ _ _ _ (hasShiftMk C A h) a b = h.add a b :=
  by
  letI := has_shift_mk C A h
  ext1
  suffices (shift_functor_add C a b).inv = (h.add a b).inv
    by
    rw [← cancel_mono (h.add a b).inv, (h.add a b).hom_inv_id, ← this, iso.hom_inv_id]
    rfl
  rfl
#align category_theory.shift_mk_core.shift_functor_add_eq CategoryTheory.ShiftMkCore.shiftFunctorAdd_eq

-- mathport name: «expr ⟦ ⟧»
notation -- Any better notational suggestions?
X "⟦" n "⟧" => (shiftFunctor _ n).obj X

-- mathport name: «expr ⟦ ⟧'»
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

variable (C)

variable [HasShift C A]

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

theorem shiftFunctorAdd'_zero_add (a : A) :
    shiftFunctorAdd' C 0 a a (zero_add a) =
      (Functor.leftUnitor _).symm ≪≫
        isoWhiskerRight (shiftFunctorZero C A).symm (shiftFunctor C a) :=
  by
  ext X
  dsimp [shift_functor_add']
  erw [obj_ε_app]
  simpa [eq_to_hom_map]
#align category_theory.shift_functor_add'_zero_add CategoryTheory.shiftFunctorAdd'_zero_add

theorem shiftFunctorAdd'_add_zero (a : A) :
    shiftFunctorAdd' C a 0 a (add_zero a) =
      (Functor.rightUnitor _).symm ≪≫
        isoWhiskerLeft (shiftFunctor C a) (shiftFunctorZero C A).symm :=
  by
  ext X
  dsimp [shift_functor_add']
  erw [ε_app_obj]
  simpa [eq_to_hom_map]
#align category_theory.shift_functor_add'_add_zero CategoryTheory.shiftFunctorAdd'_add_zero

theorem shiftFunctorAdd'_assoc (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A) (h₁₂ : a₁ + a₂ = a₁₂)
    (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) :
    shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃]) ≪≫
        isoWhiskerRight (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂) _ ≪≫ Functor.associator _ _ _ =
      shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃]) ≪≫
        isoWhiskerLeft _ (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃) :=
  by
  substs h₁₂ h₂₃ h₁₂₃
  ext X
  dsimp
  simp only [shift_functor_add'_eq_shift_functor_add, category.comp_id]
  dsimp [shift_functor_add', shift_functor_add, shift_functor]
  simp [obj_μ_inv_app, eq_to_hom_map]
#align category_theory.shift_functor_add'_assoc CategoryTheory.shiftFunctorAdd'_assoc

theorem shiftFunctorAdd_assoc (a₁ a₂ a₃ : A) :
    shiftFunctorAdd C (a₁ + a₂) a₃ ≪≫
        isoWhiskerRight (shiftFunctorAdd C a₁ a₂) _ ≪≫ Functor.associator _ _ _ =
      shiftFunctorAdd' C a₁ (a₂ + a₃) _ (add_assoc a₁ a₂ a₃).symm ≪≫
        isoWhiskerLeft _ (shiftFunctorAdd C a₂ a₃) :=
  by
  ext X
  simpa [shift_functor_add'_eq_shift_functor_add] using
    nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl))
      X
#align category_theory.shift_functor_add_assoc CategoryTheory.shiftFunctorAdd_assoc

variable {C}

theorem shiftFunctorAdd'_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).Hom.app X = (shiftFunctorZero C A).inv.app X⟦a⟧' := by
  simpa using nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_zero_add C a)) X
#align category_theory.shift_functor_add'_zero_add_hom_app CategoryTheory.shiftFunctorAdd'_zero_add_hom_app

theorem shiftFunctorAdd_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd C 0 a).Hom.app X =
      eqToHom (by dsimp <;> rw [zero_add]) ≫ (shiftFunctorZero C A).inv.app X⟦a⟧' :=
  by
  erw [← shift_functor_add'_zero_add_hom_app]
  dsimp [shift_functor_add']
  simp
#align category_theory.shift_functor_add_zero_add_hom_app CategoryTheory.shiftFunctorAdd_zero_add_hom_app

theorem shiftFunctorAdd'_zero_add_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).inv.app X = (shiftFunctorZero C A).Hom.app X⟦a⟧' :=
  by
  have := nat_trans.congr_app (congr_arg iso.inv (shift_functor_add'_zero_add C a)) X
  simp only [iso.trans_inv, iso_whisker_right_inv, iso.symm_inv, nat_trans.comp_app,
    whisker_right_app, functor.left_unitor_hom_app] at this
  dsimp at this
  simpa only [category.comp_id] using this
#align category_theory.shift_functor_add'_zero_add_inv_app CategoryTheory.shiftFunctorAdd'_zero_add_inv_app

theorem shiftFunctorAdd_zero_add_inv_app (a : A) (X : C) :
    (shiftFunctorAdd C 0 a).inv.app X =
      (shiftFunctorZero C A).Hom.app X⟦a⟧' ≫ eqToHom (by dsimp <;> rw [zero_add]) :=
  by
  erw [← shift_functor_add'_zero_add_inv_app]
  dsimp [shift_functor_add']
  simp
#align category_theory.shift_functor_add_zero_add_inv_app CategoryTheory.shiftFunctorAdd_zero_add_inv_app

theorem shiftFunctorAdd'_add_zero_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).Hom.app X = (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simpa using nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_add_zero C a)) X
#align category_theory.shift_functor_add'_add_zero_hom_app CategoryTheory.shiftFunctorAdd'_add_zero_hom_app

theorem shiftFunctorAdd_add_zero_hom_app (a : A) (X : C) :
    (shiftFunctorAdd C a 0).Hom.app X =
      eqToHom (by dsimp <;> rw [add_zero]) ≫ (shiftFunctorZero C A).inv.app (X⟦a⟧) :=
  by
  rw [← shift_functor_add'_add_zero_hom_app]
  dsimp [shift_functor_add']
  simp
#align category_theory.shift_functor_add_add_zero_hom_app CategoryTheory.shiftFunctorAdd_add_zero_hom_app

theorem shiftFunctorAdd'_add_zero_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).inv.app X = (shiftFunctorZero C A).Hom.app (X⟦a⟧) :=
  by
  have := nat_trans.congr_app (congr_arg iso.inv (shift_functor_add'_add_zero C a)) X
  simp only [iso.trans_inv, iso_whisker_left_inv, iso.symm_inv, nat_trans.comp_app,
    whisker_left_app, functor.right_unitor_hom_app] at this
  dsimp at this
  simpa only [category.comp_id] using this
#align category_theory.shift_functor_add'_add_zero_inv_app CategoryTheory.shiftFunctorAdd'_add_zero_inv_app

theorem shiftFunctorAdd_add_zero_inv_app (a : A) (X : C) :
    (shiftFunctorAdd C a 0).inv.app X =
      (shiftFunctorZero C A).Hom.app (X⟦a⟧) ≫ eqToHom (by dsimp <;> rw [add_zero]) :=
  by
  rw [← shift_functor_add'_add_zero_inv_app]
  dsimp [shift_functor_add']
  simp
#align category_theory.shift_functor_add_add_zero_inv_app CategoryTheory.shiftFunctorAdd_add_zero_inv_app

@[reassoc.1]
theorem shiftFunctorAdd'_assoc_hom_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A) (h₁₂ : a₁ + a₂ = a₁₂)
    (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).Hom.app X ≫
        (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).Hom.app X⟦a₃⟧' =
      (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).Hom.app X ≫
        (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).Hom.app (X⟦a₁⟧) :=
  by
  simpa using
    nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X
#align category_theory.shift_functor_add'_assoc_hom_app CategoryTheory.shiftFunctorAdd'_assoc_hom_app

@[reassoc.1]
theorem shiftFunctorAdd'_assoc_inv_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A) (h₁₂ : a₁ + a₂ = a₁₂)
    (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).inv.app X⟦a₃⟧' ≫
        (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).inv.app X =
      (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
        (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).inv.app X :=
  by
  simpa using
    nat_trans.congr_app (congr_arg iso.inv (shift_functor_add'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X
#align category_theory.shift_functor_add'_assoc_inv_app CategoryTheory.shiftFunctorAdd'_assoc_inv_app

@[reassoc.1]
theorem shiftFunctorAdd_assoc_hom_app (a₁ a₂ a₃ : A) (X : C) :
    (shiftFunctorAdd C (a₁ + a₂) a₃).Hom.app X ≫ (shiftFunctorAdd C a₁ a₂).Hom.app X⟦a₃⟧' =
      (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).Hom.app X ≫
        (shiftFunctorAdd C a₂ a₃).Hom.app (X⟦a₁⟧) :=
  by simpa using nat_trans.congr_app (congr_arg iso.hom (shift_functor_add_assoc C a₁ a₂ a₃)) X
#align category_theory.shift_functor_add_assoc_hom_app CategoryTheory.shiftFunctorAdd_assoc_hom_app

@[reassoc.1]
theorem shiftFunctorAdd_assoc_inv_app (a₁ a₂ a₃ : A) (X : C) :
    (shiftFunctorAdd C a₁ a₂).inv.app X⟦a₃⟧' ≫ (shiftFunctorAdd C (a₁ + a₂) a₃).inv.app X =
      (shiftFunctorAdd C a₂ a₃).inv.app (X⟦a₁⟧) ≫
        (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).inv.app X :=
  by simpa using nat_trans.congr_app (congr_arg iso.inv (shift_functor_add_assoc C a₁ a₂ a₃)) X
#align category_theory.shift_functor_add_assoc_inv_app CategoryTheory.shiftFunctorAdd_assoc_inv_app

end Defs

section AddMonoid

variable {C A} [AddMonoid A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

@[simp]
theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
  rfl
#align category_theory.has_shift.shift_obj_obj CategoryTheory.HasShift.shift_obj_obj

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _
#align category_theory.shift_add CategoryTheory.shiftAdd

theorem shift_shift' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).Hom :=
  by
  symm
  apply nat_iso.naturality_1
#align category_theory.shift_shift' CategoryTheory.shift_shift'

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftZero : X⟦0⟧ ≅ X :=
  (shiftFunctorZero C A).app _
#align category_theory.shift_zero CategoryTheory.shiftZero

theorem shift_zero' : f⟦(0 : A)⟧' = (shiftZero A X).Hom ≫ f ≫ (shiftZero A Y).inv :=
  by
  symm
  apply nat_iso.naturality_2
#align category_theory.shift_zero' CategoryTheory.shift_zero'

variable (C) {A}

/-- When `i + j = 0`, shifting by `i` and by `j` gives the identity functor -/
def shiftFunctorCompIsoId (i j : A) (h : i + j = 0) : shiftFunctor C i ⋙ shiftFunctor C j ≅ 𝟭 C :=
  (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A
#align category_theory.shift_functor_comp_iso_id CategoryTheory.shiftFunctorCompIsoId

end AddMonoid

section AddGroup

variable (C) {A} [AddGroup A] [HasShift C A]

/-- shifting by `i` and shifting by `j` forms an equivalence when `i + j = 0`. -/
@[simps]
def shiftEquiv' (i j : A) (h : i + j = 0) : C ≌ C
    where
  Functor := shiftFunctor C i
  inverse := shiftFunctor C j
  unitIso := (shiftFunctorCompIsoId C i j h).symm
  counitIso :=
    shiftFunctorCompIsoId C j i (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])
  functor_unitIso_comp' X :=
    by
    let E :=
      equiv_of_tensor_iso_unit (shift_monoidal_functor C A) ⟨i⟩ ⟨j⟩ (eq_to_iso (by ext <;> exact h))
        (eq_to_iso (by ext <;> dsimp <;> rw [← add_left_inj j, add_assoc, h, zero_add, add_zero]))
        (Subsingleton.elim _ _)
    convert equivalence.functor_unit_iso_comp E X
    all_goals
      ext X
      dsimp [shift_functor_comp_iso_id, unit_of_tensor_iso_unit, shift_functor_add']
      simpa only [eq_to_hom_map, category.assoc]
#align category_theory.shift_equiv' CategoryTheory.shiftEquiv'

/-- shifting by `n` and shifting by `-n` forms an equivalence. -/
abbrev shiftEquiv (i : A) : C ≌ C :=
  shiftEquiv' C i (-i) (add_neg_self i)
#align category_theory.shift_equiv CategoryTheory.shiftEquiv

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : IsEquivalence (shiftFunctor C i) :=
  IsEquivalence.ofEquivalence (shiftEquiv C i)

@[simp]
theorem shiftFunctor_inv (i : A) : (shiftFunctor C i).inv = shiftFunctor C (-i) :=
  rfl
#align category_theory.shift_functor_inv CategoryTheory.shiftFunctor_inv

section

variable (C)

/-- Shifting by `n` is an essentially surjective functor. -/
instance shiftFunctor_essSurj (i : A) : EssSurj (shiftFunctor C i) :=
  Equivalence.essSurj_of_equivalence _
#align category_theory.shift_functor_ess_surj CategoryTheory.shiftFunctor_essSurj

end

variable {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftShiftNeg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shiftEquiv C i).unitIso.symm.app _
#align category_theory.shift_shift_neg CategoryTheory.shiftShiftNeg

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftNegShift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shiftEquiv C i).counitIso.app _
#align category_theory.shift_neg_shift CategoryTheory.shiftNegShift

variable {X Y}

theorem shift_shift_neg' (i : A) :
    f⟦i⟧'⟦-i⟧' =
      (shiftFunctorCompIsoId C i (-i) (add_neg_self i)).Hom.app X ≫
        f ≫ (shiftFunctorCompIsoId C i (-i) (add_neg_self i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C i (-i) (add_neg_self i)) f).symm
#align category_theory.shift_shift_neg' CategoryTheory.shift_shift_neg'

theorem shift_neg_shift' (i : A) :
    f⟦-i⟧'⟦i⟧' =
      (shiftFunctorCompIsoId C (-i) i (neg_add_self i)).Hom.app X ≫
        f ≫ (shiftFunctorCompIsoId C (-i) i (neg_add_self i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C (-i) i (neg_add_self i)) f).symm
#align category_theory.shift_neg_shift' CategoryTheory.shift_neg_shift'

theorem shift_equiv_triangle (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).Hom = 𝟙 (X⟦n⟧) :=
  (shiftEquiv C n).functor_unitIso_comp X
#align category_theory.shift_equiv_triangle CategoryTheory.shift_equiv_triangle

section

theorem shift_shiftFunctorCompIsoId_hom_app (n m : A) (h : n + m = 0) (X : C) :
    (shiftFunctorCompIsoId C n m h).Hom.app X⟦n⟧' =
      (shiftFunctorCompIsoId C m n (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).Hom.app
        (X⟦n⟧) :=
  by
  dsimp [shift_functor_comp_iso_id]
  simpa only [functor.map_comp, ← shift_functor_add'_zero_add_inv_app n X, ←
    shift_functor_add'_add_zero_inv_app n X] using
    shift_functor_add'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg]) (by rw [h, zero_add]) X
#align category_theory.shift_shift_functor_comp_iso_id_hom_app CategoryTheory.shift_shiftFunctorCompIsoId_hom_app

theorem shift_shiftFunctorCompIsoId_inv_app (n m : A) (h : n + m = 0) (X : C) :
    (shiftFunctorCompIsoId C n m h).inv.app X⟦n⟧' =
      (shiftFunctorCompIsoId C m n (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).inv.app
        (X⟦n⟧) :=
  by
  rw [← cancel_mono ((shift_functor_comp_iso_id C n m h).Hom.app X⟦n⟧'), ← functor.map_comp,
    iso.inv_hom_id_app, Functor.map_id, shift_shift_functor_comp_iso_id_hom_app, iso.inv_hom_id_app]
  rfl
#align category_theory.shift_shift_functor_comp_iso_id_inv_app CategoryTheory.shift_shiftFunctorCompIsoId_inv_app

theorem shift_shiftFunctorCompIsoId_add_neg_self_hom_app (n : A) (X : C) :
    (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).Hom.app X⟦n⟧' =
      (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).Hom.app (X⟦n⟧) :=
  by apply shift_shift_functor_comp_iso_id_hom_app
#align category_theory.shift_shift_functor_comp_iso_id_add_neg_self_hom_app CategoryTheory.shift_shiftFunctorCompIsoId_add_neg_self_hom_app

theorem shift_shiftFunctorCompIsoId_add_neg_self_inv_app (n : A) (X : C) :
    (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.app X⟦n⟧' =
      (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).inv.app (X⟦n⟧) :=
  by apply shift_shift_functor_comp_iso_id_inv_app
#align category_theory.shift_shift_functor_comp_iso_id_add_neg_self_inv_app CategoryTheory.shift_shiftFunctorCompIsoId_add_neg_self_inv_app

theorem shift_shiftFunctorCompIsoId_neg_add_self_hom_app (n : A) (X : C) :
    (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).Hom.app X⟦-n⟧' =
      (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).Hom.app (X⟦-n⟧) :=
  by apply shift_shift_functor_comp_iso_id_hom_app
#align category_theory.shift_shift_functor_comp_iso_id_neg_add_self_hom_app CategoryTheory.shift_shiftFunctorCompIsoId_neg_add_self_hom_app

theorem shift_shiftFunctorCompIsoId_neg_add_self_inv_app (n : A) (X : C) :
    (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).inv.app X⟦-n⟧' =
      (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.app (X⟦-n⟧) :=
  by apply shift_shift_functor_comp_iso_id_inv_app
#align category_theory.shift_shift_functor_comp_iso_id_neg_add_self_inv_app CategoryTheory.shift_shiftFunctorCompIsoId_neg_add_self_inv_app

end

variable {A C}

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _
#align category_theory.shift_zero_eq_zero CategoryTheory.shift_zero_eq_zero

end AddGroup

section AddCommMonoid

variable (C) {A} [AddCommMonoid A] [HasShift C A]

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shiftFunctorComm (i j : A) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅ shiftFunctor C j ⋙ shiftFunctor C i :=
  (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)
#align category_theory.shift_functor_comm CategoryTheory.shiftFunctorComm

theorem shiftFunctorComm_eq (i j k : A) (h : i + j = k) :
    shiftFunctorComm C i j =
      (shiftFunctorAdd' C i j k h).symm ≪≫ shiftFunctorAdd' C j i k (by rw [add_comm j i, h]) :=
  by
  subst h
  rw [shift_functor_add'_eq_shift_functor_add]
  rfl
#align category_theory.shift_functor_comm_eq CategoryTheory.shiftFunctorComm_eq

theorem shiftFunctorComm_symm (i j : A) : (shiftFunctorComm C i j).symm = shiftFunctorComm C j i :=
  by
  ext1
  dsimp
  simpa only [shift_functor_comm_eq C i j (i + j) rfl,
    shift_functor_comm_eq C j i (i + j) (add_comm j i)]
#align category_theory.shift_functor_comm_symm CategoryTheory.shiftFunctorComm_symm

variable {C} (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
abbrev shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftFunctorComm C i j).app X
#align category_theory.shift_comm CategoryTheory.shiftComm

@[simp]
theorem shiftComm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i :=
  by
  ext1
  exact nat_trans.congr_app (congr_arg iso.hom (shift_functor_comm_symm C i j)) X
#align category_theory.shift_comm_symm CategoryTheory.shiftComm_symm

variable {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shift_comm' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).Hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).Hom :=
  by
  erw [← shift_comm_symm Y i j, ← (shift_functor_comm C i j).Hom.naturality_assoc f,
    iso.hom_inv_id_app, category.comp_id]
  rfl
#align category_theory.shift_comm' CategoryTheory.shift_comm'

@[reassoc.1]
theorem shiftComm_hom_comp (i j : A) :
    (shiftComm X i j).Hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).Hom := by
  rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]
#align category_theory.shift_comm_hom_comp CategoryTheory.shiftComm_hom_comp

theorem shiftFunctorZero_hom_app_shift (n : A) :
    (shiftFunctorZero C A).Hom.app (X⟦n⟧) =
      (shiftFunctorComm C n 0).Hom.app X ≫ (shiftFunctorZero C A).Hom.app X⟦n⟧' :=
  by
  rw [← shift_functor_add'_zero_add_inv_app n X, shift_functor_comm_eq C n 0 n (add_zero n)]
  dsimp
  rw [category.assoc, iso.hom_inv_id_app, category.comp_id, shift_functor_add'_add_zero_inv_app]
#align category_theory.shift_functor_zero_hom_app_shift CategoryTheory.shiftFunctorZero_hom_app_shift

theorem shiftFunctorZero_inv_app_shift (n : A) :
    (shiftFunctorZero C A).inv.app (X⟦n⟧) =
      (shiftFunctorZero C A).inv.app X⟦n⟧' ≫ (shiftFunctorComm C n 0).inv.app X :=
  by
  rw [← cancel_mono ((shift_functor_zero C A).Hom.app (X⟦n⟧)), category.assoc, iso.inv_hom_id_app,
    shift_functor_zero_hom_app_shift, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id]
#align category_theory.shift_functor_zero_inv_app_shift CategoryTheory.shiftFunctorZero_inv_app_shift

@[reassoc.1]
theorem shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app (m₁ m₂ m₃ : A) (X : C) :
    (shiftFunctorComm C m₁ (m₂ + m₃)).Hom.app X ≫ (shiftFunctorAdd C m₂ m₃).Hom.app X⟦m₁⟧' =
      (shiftFunctorAdd C m₂ m₃).Hom.app (X⟦m₁⟧) ≫
        (shiftFunctorComm C m₁ m₂).Hom.app X⟦m₃⟧' ≫ (shiftFunctorComm C m₁ m₃).Hom.app (X⟦m₂⟧) :=
  by
  simp only [← cancel_mono ((shift_functor_comm C m₁ m₃).inv.app (X⟦m₂⟧)), ←
    cancel_mono ((shift_functor_comm C m₁ m₂).inv.app X⟦m₃⟧'), category.assoc, iso.hom_inv_id_app]
  dsimp
  simp only [category.id_comp, ← functor.map_comp, iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, category.comp_id, shift_functor_comm_eq C _ _ _ rfl, ←
    shift_functor_add'_eq_shift_functor_add]
  dsimp
  simp only [category.assoc, iso.hom_inv_id_app_assoc, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    shift_functor_add'_assoc_hom_app_assoc m₂ m₃ m₁ (m₂ + m₃) (m₁ + m₃) (m₁ + (m₂ + m₃)) rfl
      (add_comm m₃ m₁) (add_comm _ m₁) X,
    ←
    shift_functor_add'_assoc_hom_app_assoc m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃) (m₁ + (m₂ + m₃))
      (add_comm _ _) rfl (by rw [add_comm m₂ m₁, add_assoc]) X,
    shift_functor_add'_assoc_hom_app m₁ m₂ m₃ (m₁ + m₂) (m₂ + m₃) (m₁ + (m₂ + m₃)) rfl rfl
      (add_assoc _ _ _) X]
#align category_theory.shift_functor_comm_hom_app_comp_shift_shift_functor_add_hom_app CategoryTheory.shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app

end AddCommMonoid

variable {C A} {D : Type _} [Category D] [AddMonoid A] [HasShift D A]

variable (F : C ⥤ D) [Full F] [Faithful F]

section

variable (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

include F s i

/-- auxiliary definition for `has_shift_of_fully_faithful` -/
def hasShiftOfFullyFaithfulZero : s 0 ≅ 𝟭 C :=
  natIsoOfCompFullyFaithful F
    (i 0 ≪≫
      isoWhiskerLeft F (shiftFunctorZero D A) ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
#align category_theory.has_shift_of_fully_faithful_zero CategoryTheory.hasShiftOfFullyFaithfulZero

@[simp]
theorem map_hasShiftOfFullyFaithfulZero_hom_app (X : C) :
    F.map ((hasShiftOfFullyFaithfulZero F s i).Hom.app X) =
      (i 0).Hom.app X ≫ (shiftFunctorZero D A).Hom.app (F.obj X) :=
  by
  dsimp [has_shift_of_fully_faithful_zero]
  simp
#align category_theory.map_has_shift_of_fully_faithful_zero_hom_app CategoryTheory.map_hasShiftOfFullyFaithfulZero_hom_app

@[simp]
theorem map_hasShiftOfFullyFaithfulZero_inv_app (X : C) :
    F.map ((hasShiftOfFullyFaithfulZero F s i).inv.app X) =
      (shiftFunctorZero D A).inv.app (F.obj X) ≫ (i 0).inv.app X :=
  by
  dsimp [has_shift_of_fully_faithful_zero]
  simp
#align category_theory.map_has_shift_of_fully_faithful_zero_inv_app CategoryTheory.map_hasShiftOfFullyFaithfulZero_inv_app

/-- auxiliary definition for `has_shift_of_fully_faithful` -/
def hasShiftOfFullyFaithfulAdd (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  natIsoOfCompFullyFaithful F
    (i (a + b) ≪≫
      isoWhiskerLeft _ (shiftFunctorAdd D a b) ≪≫
        (Functor.associator _ _ _).symm ≪≫
          isoWhiskerRight (i a).symm _ ≪≫
            Functor.associator _ _ _ ≪≫
              isoWhiskerLeft _ (i b).symm ≪≫ (Functor.associator _ _ _).symm)
#align category_theory.has_shift_of_fully_faithful_add CategoryTheory.hasShiftOfFullyFaithfulAdd

@[simp]
theorem map_hasShiftOfFullyFaithfulAdd_hom_app (a b : A) (X : C) :
    F.map ((hasShiftOfFullyFaithfulAdd F s i a b).Hom.app X) =
      (i (a + b)).Hom.app X ≫
        (shiftFunctorAdd D a b).Hom.app (F.obj X) ≫
          (i a).inv.app X⟦b⟧' ≫ (i b).inv.app ((s a).obj X) :=
  by
  dsimp [has_shift_of_fully_faithful_add]
  simp
#align category_theory.map_has_shift_of_fully_faithful_add_hom_app CategoryTheory.map_hasShiftOfFullyFaithfulAdd_hom_app

@[simp]
theorem map_hasShiftOfFullyFaithfulAdd_inv_app (a b : A) (X : C) :
    F.map ((hasShiftOfFullyFaithfulAdd F s i a b).inv.app X) =
      (i b).Hom.app ((s a).obj X) ≫
        (i a).Hom.app X⟦b⟧' ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) ≫ (i (a + b)).inv.app X :=
  by
  dsimp [has_shift_of_fully_faithful_add]
  simp
#align category_theory.map_has_shift_of_fully_faithful_add_inv_app CategoryTheory.map_hasShiftOfFullyFaithfulAdd_inv_app

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def hasShiftOfFullyFaithful : HasShift C A :=
  hasShiftMk C A
    { f := s
      zero := hasShiftOfFullyFaithfulZero F s i
      add := hasShiftOfFullyFaithfulAdd F s i
      assoc_hom_app := fun m₁ m₂ m₃ X =>
        F.map_injective
          (by
            rw [← cancel_mono ((i m₃).Hom.app ((s m₂).obj ((s m₁).obj X)))]
            simp only [functor.map_comp, map_has_shift_of_fully_faithful_add_hom_app,
              category.assoc, iso.inv_hom_id_app_assoc, iso.inv_hom_id_app]
            erw [(i m₃).Hom.naturality]
            have := dcongr_arg (fun a => (i a).Hom.app X) (add_assoc m₁ m₂ m₃)
            dsimp at this
            dsimp
            rw [iso.inv_hom_id_app_assoc, map_has_shift_of_fully_faithful_add_hom_app, this,
              eq_to_hom_map, category.comp_id, ← functor.map_comp, category.assoc,
              iso.inv_hom_id_app_assoc, functor.map_comp, functor.map_comp,
              shift_functor_add_assoc_hom_app_assoc m₁ m₂ m₃ (F.obj X)]
            dsimp [shift_functor_add']
            simp only [eq_to_hom_app, category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl,
              category.id_comp, nat_trans.naturality_assoc, functor.comp_map])
      zero_add_hom_app := fun n X =>
        F.map_injective
          (by
            have := dcongr_arg (fun a => (i a).Hom.app X) (zero_add n)
            dsimp at this
            rw [← cancel_mono ((i n).Hom.app ((s 0).obj X))]
            simp only [this, map_has_shift_of_fully_faithful_add_hom_app,
              shift_functor_add_zero_add_hom_app, eq_to_hom_map, category.assoc,
              eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp, iso.inv_hom_id_app,
              functor.map_comp]
            erw [(i n).Hom.naturality]
            dsimp
            simp)
      add_zero_hom_app := fun n X =>
        F.map_injective
          (by
            have := dcongr_arg (fun a => (i a).Hom.app X) (add_zero n)
            dsimp at this
            simpa [this, ← nat_trans.naturality_assoc, eq_to_hom_map,
              shift_functor_add_add_zero_hom_app] ) }
#align category_theory.has_shift_of_fully_faithful CategoryTheory.hasShiftOfFullyFaithful

end

end CategoryTheory

