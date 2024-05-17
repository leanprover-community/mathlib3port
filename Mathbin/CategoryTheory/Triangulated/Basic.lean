/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Algebra.Ring.Int
import CategoryTheory.Shift.Basic

#align_import category_theory.triangulated.basic from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Triangles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of triangles in an additive category with an additive shift.
It also defines morphisms between these triangles.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

/-
We work in a category `C` equipped with a shift.
-/
variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

#print CategoryTheory.Pretriangulated.Triangle /-
/-- A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
See <https://stacks.math.columbia.edu/tag/0144>.
-/
structure Triangle where mk' ::
  obj₁ : C
  obj₂ : C
  obj₃ : C
  mor₁ : obj₁ ⟶ obj₂
  mor₂ : obj₂ ⟶ obj₃
  mor₃ : obj₃ ⟶ obj₁⟦(1 : ℤ)⟧
#align category_theory.pretriangulated.triangle CategoryTheory.Pretriangulated.Triangle
-/

variable {C}

#print CategoryTheory.Pretriangulated.Triangle.mk /-
/-- A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
def Triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle C
    where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h
#align category_theory.pretriangulated.triangle.mk CategoryTheory.Pretriangulated.Triangle.mk
-/

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open scoped ZeroObject

instance : Inhabited (Triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

#print CategoryTheory.Pretriangulated.contractibleTriangle /-
/-- For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps]
def contractibleTriangle (X : C) : Triangle C :=
  Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0
#align category_theory.pretriangulated.contractible_triangle CategoryTheory.Pretriangulated.contractibleTriangle
-/

end

#print CategoryTheory.Pretriangulated.TriangleMorphism /-
/-- A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f      g      h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧'
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f'     g'     h'
```
See <https://stacks.math.columbia.edu/tag/0144>.
-/
@[ext]
structure TriangleMorphism (T₁ : Triangle C) (T₂ : Triangle C) where
  hom₁ : T₁.obj₁ ⟶ T₂.obj₁
  hom₂ : T₁.obj₂ ⟶ T₂.obj₂
  hom₃ : T₁.obj₃ ⟶ T₂.obj₃
  comm₁' : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁ := by obviously
  comm₂' : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂ := by obviously
  comm₃' : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃ := by obviously
#align category_theory.pretriangulated.triangle_morphism CategoryTheory.Pretriangulated.TriangleMorphism
-/

attribute [simp, reassoc] triangle_morphism.comm₁ triangle_morphism.comm₂ triangle_morphism.comm₃

#print CategoryTheory.Pretriangulated.triangleMorphismId /-
/-- The identity triangle morphism.
-/
@[simps]
def triangleMorphismId (T : Triangle C) : TriangleMorphism T T
    where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃
#align category_theory.pretriangulated.triangle_morphism_id CategoryTheory.Pretriangulated.triangleMorphismId
-/

instance (T : Triangle C) : Inhabited (TriangleMorphism T T) :=
  ⟨triangleMorphismId T⟩

variable {T₁ T₂ T₃ : Triangle C}

#print CategoryTheory.Pretriangulated.TriangleMorphism.comp /-
/-- Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
    TriangleMorphism T₁ T₃ where
  hom₁ := f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃
#align category_theory.pretriangulated.triangle_morphism.comp CategoryTheory.Pretriangulated.TriangleMorphism.comp
-/

#print CategoryTheory.Pretriangulated.triangleCategory /-
/-- Triangles with triangle morphisms form a category.
-/
@[simps]
instance triangleCategory : Category (Triangle C)
    where
  Hom A B := TriangleMorphism A B
  id A := triangleMorphismId A
  comp A B C f g := f.comp g
#align category_theory.pretriangulated.triangle_category CategoryTheory.Pretriangulated.triangleCategory
-/

#print CategoryTheory.Pretriangulated.Triangle.homMk /-
/-- a constructor for morphisms of triangles -/
@[simps]
def Triangle.homMk (A B : Triangle C) (hom₁ : A.obj₁ ⟶ B.obj₁) (hom₂ : A.obj₂ ⟶ B.obj₂)
    (hom₃ : A.obj₃ ⟶ B.obj₃) (comm₁ : A.mor₁ ≫ hom₂ = hom₁ ≫ B.mor₁)
    (comm₂ : A.mor₂ ≫ hom₃ = hom₂ ≫ B.mor₂) (comm₃ : A.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ B.mor₃) : A ⟶ B :=
  { hom₁
    hom₂
    hom₃
    comm₁' := comm₁
    comm₂' := comm₂
    comm₃' := comm₃ }
#align category_theory.pretriangulated.triangle.hom_mk CategoryTheory.Pretriangulated.Triangle.homMk
-/

#print CategoryTheory.Pretriangulated.Triangle.isoMk /-
/-- a constructor for isomorphisms of triangles -/
@[simps]
def Triangle.isoMk (A B : Triangle C) (iso₁ : A.obj₁ ≅ B.obj₁) (iso₂ : A.obj₂ ≅ B.obj₂)
    (iso₃ : A.obj₃ ≅ B.obj₃) (comm₁ : A.mor₁ ≫ iso₂.Hom = iso₁.Hom ≫ B.mor₁)
    (comm₂ : A.mor₂ ≫ iso₃.Hom = iso₂.Hom ≫ B.mor₂)
    (comm₃ : A.mor₃ ≫ iso₁.Hom⟦1⟧' = iso₃.Hom ≫ B.mor₃) : A ≅ B
    where
  Hom := Triangle.homMk _ _ iso₁.Hom iso₂.Hom iso₃.Hom comm₁ comm₂ comm₃
  inv :=
    Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
      (by
        simp only [← cancel_mono iso₂.hom, assoc, iso.inv_hom_id, comp_id, comm₁,
          iso.inv_hom_id_assoc])
      (by
        simp only [← cancel_mono iso₃.hom, assoc, iso.inv_hom_id, comp_id, comm₂,
          iso.inv_hom_id_assoc])
      (by
        simp only [← cancel_mono (iso₁.hom⟦(1 : ℤ)⟧'), assoc, ← functor.map_comp, iso.inv_hom_id,
          CategoryTheory.Functor.map_id, comp_id, comm₃, iso.inv_hom_id_assoc])
#align category_theory.pretriangulated.triangle.iso_mk CategoryTheory.Pretriangulated.Triangle.isoMk
-/

end CategoryTheory.Pretriangulated

