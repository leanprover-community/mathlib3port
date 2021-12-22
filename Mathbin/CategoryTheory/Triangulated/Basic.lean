import Mathbin.CategoryTheory.Shift

/-!
# Triangles

This file contains the definition of triangles in an additive category with an additive shift.
It also defines morphisms between these triangles.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Triangulated

open CategoryTheory.Category

variable (C : Type u) [category.{v} C] [has_shift C]

/-- 
A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
See https://stacks.math.columbia.edu/tag/0144.
-/
structure triangle where mk' ::
  obj₁ : C
  obj₂ : C
  obj₃ : C
  mor₁ : obj₁ ⟶ obj₂
  mor₂ : obj₂ ⟶ obj₃
  mor₃ : obj₃ ⟶ obj₁⟦1⟧

/-- 
A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
def triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧) : triangle C :=
  { obj₁ := X, obj₂ := Y, obj₃ := Z, mor₁ := f, mor₂ := g, mor₃ := h }

section

variable [has_zero_object C] [has_zero_morphisms C]

open_locale ZeroObject

instance : Inhabited (triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- 
For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps]
def contractible_triangle (X : C) : triangle C :=
  triangle.mk C (𝟙 X) (0 : X ⟶ 0) 0

end

variable {C}

/-- 
A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
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
See https://stacks.math.columbia.edu/tag/0144.
-/
@[ext]
structure triangle_morphism (T₁ : triangle C) (T₂ : triangle C) where
  hom₁ : T₁.obj₁ ⟶ T₂.obj₁
  hom₂ : T₁.obj₂ ⟶ T₂.obj₂
  hom₃ : T₁.obj₃ ⟶ T₂.obj₃
  comm₁' : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁ := by
    run_tac
      obviously
  comm₂' : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂ := by
    run_tac
      obviously
  comm₃' : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃ := by
    run_tac
      obviously

restate_axiom triangle_morphism.comm₁'

restate_axiom triangle_morphism.comm₂'

restate_axiom triangle_morphism.comm₃'

attribute [simp, reassoc] triangle_morphism.comm₁ triangle_morphism.comm₂ triangle_morphism.comm₃

/-- 
The identity triangle morphism.
-/
@[simps]
def triangle_morphism_id (T : triangle C) : triangle_morphism T T :=
  { hom₁ := 𝟙 T.obj₁, hom₂ := 𝟙 T.obj₂, hom₃ := 𝟙 T.obj₃ }

instance (T : triangle C) : Inhabited (triangle_morphism T T) :=
  ⟨triangle_morphism_id T⟩

variable {T₁ T₂ T₃ : triangle C}

/-- 
Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
def triangle_morphism.comp (f : triangle_morphism T₁ T₂) (g : triangle_morphism T₂ T₃) : triangle_morphism T₁ T₃ :=
  { hom₁ := f.hom₁ ≫ g.hom₁, hom₂ := f.hom₂ ≫ g.hom₂, hom₃ := f.hom₃ ≫ g.hom₃ }

-- failed to format: format: uncaught backtrack exception
/--
      Triangles with triangle morphisms form a category.
      -/
    @[ simps ]
  instance
    triangle_category
    : category ( triangle C )
    where Hom A B := triangle_morphism A B id A := triangle_morphism_id A comp A B C f g := f.comp g

end CategoryTheory.Triangulated

