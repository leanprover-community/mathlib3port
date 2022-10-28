/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.PathCategory
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Combinatorics.Quiver.Path

/-!
# Vertex group

This file defines the vertex group (*aka* isotropy group) of a groupoid at a vertex.

## Implementation notes

* The instance is defined "manually", instead of relying on `category_theory.Aut.group` or
  using `category_theory.inv`.
* The multiplication order therefore matches the categorical one : `x * y = x ≫ y`.
* The inverse is directly defined in terms of the groupoidal inverse : `x ⁻¹ = groupoid.inv x`.

## Tags

isotropy, vertex group, groupoid
-/


namespace CategoryTheory

namespace Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- The vertex group at `c`. -/
@[simps]
instance vertexGroup (c : C) : Group (c ⟶ c) where
  mul := fun x y : c ⟶ c => x ≫ y
  mul_assoc := Category.assoc
  one := 𝟙 c
  one_mul := Category.id_comp
  mul_one := Category.comp_id
  inv := Groupoid.inv
  mul_left_inv := inv_comp

/-- The inverse in the group is equal to the inverse given by `category_theory.inv`. -/
theorem vertexGroup.inv_eq_inv (c : C) (γ : c ⟶ c) : γ⁻¹ = CategoryTheory.inv γ :=
  Groupoid.inv_eq_inv γ

/-- An arrow in the groupoid defines, by conjugation, an isomorphism of groups between
its endpoints.
-/
@[simps]
def vertexGroupIsomOfMap {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) where
  toFun γ := inv f ≫ γ ≫ f
  invFun δ := f ≫ δ ≫ inv f
  left_inv γ := by simp_rw [category.assoc, comp_inv, category.comp_id, ← category.assoc, comp_inv, category.id_comp]
  right_inv δ := by simp_rw [category.assoc, inv_comp, ← category.assoc, inv_comp, category.id_comp, category.comp_id]
  map_mul' γ₁ γ₂ := by simp only [vertex_group_mul, inv_eq_inv, category.assoc, is_iso.hom_inv_id_assoc]

/-- A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertexGroupIsomOfPath {c d : C} (p : Quiver.Path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
  vertexGroupIsomOfMap (composePath p)

/-- A functor defines a morphism of vertex group. -/
@[simps]
def _root_.category_theory.functor.map_vertex_group {D : Type v} [Groupoid D] (φ : C ⥤ D) (c : C) :
    (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) where
  toFun := φ.map
  map_one' := φ.map_id c
  map_mul' := φ.map_comp

end Groupoid

end CategoryTheory

