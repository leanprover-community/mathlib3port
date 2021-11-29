import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor 
import Mathbin.CategoryTheory.Shift 
import Mathbin.CategoryTheory.Triangulated.Rotate

/-!
# Pretriangulated Categories

This file contains the definition of pretriangulated categories and triangulated functors
between them.

## Implementation Notes

We work under the assumption that pretriangulated categories are preadditive categories,
but not necessarily additive categories, as is assumed in some sources.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Triangulated

open CategoryTheory.Category

variable(C : Type u)[category.{v} C][has_zero_object C][has_shift C][preadditive C][functor.additive (shift C).Functor]

/--
A preadditive category `C` with an additive shift, and a class of "distinguished triangles"
relative to that shift is called pretriangulated if the following hold:
* Any triangle that is isomorphic to a distinguished triangle is also distinguished.
* Any triangle of the form `(X,X,0,id,0,0)` is distinguished.
* For any morphism `f : X ⟶ Y` there exists a distinguished triangle of the form `(X,Y,Z,f,g,h)`.
* The triangle `(X,Y,Z,f,g,h)` is distinguished if and only if `(Y,Z,X⟦1⟧,g,h,-f⟦1⟧)` is.
* Given a diagram:
  ```
        f       g       h
    X  ───> Y  ───> Z  ───> X⟦1⟧
    │       │                │
    │a      │b               │a⟦1⟧'
    V       V                V
    X' ───> Y' ───> Z' ───> X'⟦1⟧
        f'      g'      h'
  ```
  where the left square commutes, and whose rows are distinguished triangles,
  there exists a morphism `c : Z ⟶ Z'` such that `(a,b,c)` is a triangle morphism.
See https://stacks.math.columbia.edu/tag/0145
-/
class pretriangulated where 
  DistinguishedTriangles{} : Set (triangle C)
  isomorphic_distinguished :
  ∀ T₁ (_ : T₁ ∈ distinguished_triangles) (T₂ : triangle C) T₁ (_ : T₁ ≅ T₂), T₂ ∈ distinguished_triangles 
  contractible_distinguished : ∀ (X : C), contractible_triangle C X ∈ distinguished_triangles 
  distinguished_cocone_triangle :
  ∀ (X Y : C) (f : X ⟶ Y), ∃ (Z : C)(g : Y ⟶ Z)(h : Z ⟶ X⟦1⟧), triangle.mk _ f g h ∈ distinguished_triangles 
  rotate_distinguished_triangle : ∀ (T : triangle C), T ∈ distinguished_triangles ↔ T.rotate ∈ distinguished_triangles 
  complete_distinguished_triangle_morphism :
  ∀ (T₁ T₂ : triangle C) (h₁ : T₁ ∈ distinguished_triangles) (h₂ : T₂ ∈ distinguished_triangles) (a : T₁.obj₁ ⟶ T₂.obj₁)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃

namespace Pretriangulated

variable[pretriangulated C]

notation:20 "dist_triang" C => distinguished_triangles C

/--
Given any distinguished triangle `T`, then we know `T.rotate` is also distinguished.
-/
theorem rot_of_dist_triangle T (_ : T ∈ (dist_triang C)) : T.rotate ∈ (dist_triang C) :=
  (rotate_distinguished_triangle T).mp H

/--
Given any distinguished triangle `T`, then we know `T.inv_rotate` is also distinguished.
-/
theorem inv_rot_of_dist_triangle T (_ : T ∈ (dist_triang C)) : T.inv_rotate ∈ (dist_triang C) :=
  (rotate_distinguished_triangle T.inv_rotate).mpr
    (isomorphic_distinguished T H T.inv_rotate.rotate T (inv_rot_comp_rot.symm.app T))

-- error in CategoryTheory.Triangulated.Pretriangulated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
theorem comp_dist_triangle_mor_zero₁₂ (T «expr ∈ » «exprdist_triang »(C)) : «expr = »(«expr ≫ »(T.mor₁, T.mor₂), 0) :=
begin
  have [ident h] [] [":=", expr contractible_distinguished T.obj₁],
  have [ident f] [] [":=", expr complete_distinguished_triangle_morphism],
  specialize [expr f (contractible_triangle C T.obj₁) T h H («expr𝟙»() T.obj₁) T.mor₁],
  have [ident t] [":", expr «expr = »(«expr ≫ »((contractible_triangle C T.obj₁).mor₁, T.mor₁), «expr ≫ »(«expr𝟙»() T.obj₁, T.mor₁))] [],
  by refl,
  specialize [expr f t],
  cases [expr f] ["with", ident c, ident f],
  rw ["<-", expr f.left] [],
  simp [] [] ["only"] ["[", expr limits.zero_comp, ",", expr contractible_triangle_mor₂, "]"] [] []
end

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
theorem comp_dist_triangle_mor_zero₂₃ T (_ : T ∈ (dist_triang C)) : T.mor₂ ≫ T.mor₃ = 0 :=
  comp_dist_triangle_mor_zero₁₂ C T.rotate (rot_of_dist_triangle C T H)

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `h ≫ f⟦1⟧ = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
theorem comp_dist_triangle_mor_zero₃₁ T (_ : T ∈ (dist_triang C)) : T.mor₃ ≫ (shift C).Functor.map T.mor₁ = 0 :=
  have H₂ := rot_of_dist_triangle C T.rotate (rot_of_dist_triangle C T H)
  by 
    simpa using comp_dist_triangle_mor_zero₁₂ C T.rotate.rotate H₂

end Pretriangulated

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated

namespace Pretriangulated

variable(C :
    Type
      u₁)[category.{v₁}
      C][has_zero_object
      C][has_shift C][preadditive C][functor.additive (shift C).Functor][functor.additive (shift C).inverse]

variable(D :
    Type
      u₂)[category.{v₂}
      D][has_zero_object
      D][has_shift D][preadditive D][functor.additive (shift D).Functor][functor.additive (shift D).inverse]

/--
The underlying structure of a triangulated functor between pretriangulated categories `C` and `D`
is a functor `F : C ⥤ D` together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧`.
-/
structure triangulated_functor_struct extends C ⥤ D where 
  commShift : (shift C).Functor ⋙ to_functor ≅ to_functor ⋙ (shift D).Functor

instance  : Inhabited (triangulated_functor_struct C C) :=
  ⟨{ obj := fun X => X, map := fun _ _ f => f,
      commShift :=
        by 
          rfl }⟩

variable{C D}

/--
Given a `triangulated_functor_struct` we can define a function from triangles of `C` to
triangles of `D`.
-/
@[simp]
def triangulated_functor_struct.map_triangle (F : triangulated_functor_struct C D) (T : triangle C) : triangle D :=
  triangle.mk _ (F.map T.mor₁) (F.map T.mor₂) (F.map T.mor₃ ≫ F.comm_shift.hom.app T.obj₁)

variable(C D)

/--
A triangulated functor between pretriangulated categories `C` and `D` is a functor `F : C ⥤ D`
together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧` such that for every
distinguished triangle `(X,Y,Z,f,g,h)` of `C`, the triangle
`(F(X), F(Y), F(Z), F(f), F(g), F(h) ≫ (ξ X))` is a distinguished triangle of `D`.
See https://stacks.math.columbia.edu/tag/014V
-/
structure triangulated_functor[pretriangulated C][pretriangulated D] extends triangulated_functor_struct C D where 
  map_distinguished' :
  ∀ (T : triangle C), T ∈ (dist_triang C) → to_triangulated_functor_struct.map_triangle T ∈ (dist_triang D)

instance  [pretriangulated C] : Inhabited (triangulated_functor C C) :=
  ⟨{ obj := fun X => X, map := fun _ _ f => f,
      commShift :=
        by 
          rfl,
      map_distinguished' :=
        by 
          rintro ⟨_, _, _, _⟩ Tdt 
          dsimp  at *
          rwa [category.comp_id] }⟩

variable{C D}[pretriangulated C][pretriangulated D]

/--
Given a `triangulated_functor` we can define a function from triangles of `C` to triangles of `D`.
-/
@[simp]
def triangulated_functor.map_triangle (F : triangulated_functor C D) (T : triangle C) : triangle D :=
  triangle.mk _ (F.map T.mor₁) (F.map T.mor₂) (F.map T.mor₃ ≫ F.comm_shift.hom.app T.obj₁)

/--
Given a `triangulated_functor` and a distinguished triangle `T` of `C`, then the triangle it
maps onto in `D` is also distinguished.
-/
theorem triangulated_functor.map_distinguished (F : triangulated_functor C D) (T : triangle C)
  (h : T ∈ (dist_triang C)) : F.map_triangle T ∈ (dist_triang D) :=
  F.map_distinguished' T h

end Pretriangulated

end CategoryTheory.Triangulated

