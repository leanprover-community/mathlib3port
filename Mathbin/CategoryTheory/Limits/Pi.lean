import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ pi.eval C i`, we can produce a
   `has_limit F` instance
-/


open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I → Type u₁} [∀ i, category.{v₁} (C i)]

variable {J : Type v₁} [small_category J]

variable {F : J ⥤ ∀ i, C i}

/-- A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ pi.eval C i`.
-/
def cone_comp_eval (c : cone F) (i : I) : cone (F ⋙ pi.eval C i) where
  x := c.X i
  π := { app := fun j => c.π.app j i, naturality' := fun j j' f => congr_funₓ (c.π.naturality f) i }

/-- A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ pi.eval C i`.
-/
def cocone_comp_eval (c : cocone F) (i : I) : cocone (F ⋙ pi.eval C i) where
  x := c.X i
  ι := { app := fun j => c.ι.app j i, naturality' := fun j j' f => congr_funₓ (c.ι.naturality f) i }

/-- Given a family of cones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cone F`.
-/
def cone_of_cone_comp_eval (c : ∀ i, cone (F ⋙ pi.eval C i)) : cone F where
  x := fun i => (c i).x
  π :=
    { app := fun j i => (c i).π.app j,
      naturality' := fun j j' f => by
        ext i
        exact (c i).π.naturality f }

/-- Given a family of cocones over the `F ⋙ pi.eval C i`,
we can assemble these together as a `cocone F`.
-/
def cocone_of_cocone_comp_eval (c : ∀ i, cocone (F ⋙ pi.eval C i)) : cocone F where
  x := fun i => (c i).x
  ι :=
    { app := fun j i => (c i).ι.app j,
      naturality' := fun j j' f => by
        ext i
        exact (c i).ι.naturality f }

/-- Given a family of limit cones over the `F ⋙ pi.eval C i`,
assembling them together as a `cone F` produces a limit cone.
-/
def cone_of_cone_eval_is_limit {c : ∀ i, cone (F ⋙ pi.eval C i)} (P : ∀ i, is_limit (c i)) :
    is_limit (cone_of_cone_comp_eval c) where
  lift := fun s i => (P i).lift (cone_comp_eval s i)
  fac' := fun s j => by
    ext i
    exact (P i).fac (cone_comp_eval s i) j
  uniq' := fun s m w => by
    ext i
    exact (P i).uniq (cone_comp_eval s i) (m i) fun j => congr_funₓ (w j) i

/-- Given a family of colimit cocones over the `F ⋙ pi.eval C i`,
assembling them together as a `cocone F` produces a colimit cocone.
-/
def cocone_of_cocone_eval_is_colimit {c : ∀ i, cocone (F ⋙ pi.eval C i)} (P : ∀ i, is_colimit (c i)) :
    is_colimit (cocone_of_cocone_comp_eval c) where
  desc := fun s i => (P i).desc (cocone_comp_eval s i)
  fac' := fun s j => by
    ext i
    exact (P i).fac (cocone_comp_eval s i) j
  uniq' := fun s m w => by
    ext i
    exact (P i).uniq (cocone_comp_eval s i) (m i) fun j => congr_funₓ (w j) i

section

variable [∀ i, has_limit (F ⋙ pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ pi.eval C i`,
then `F` has a limit.
-/
theorem has_limit_of_has_limit_comp_eval : has_limit F :=
  has_limit.mk
    { Cone := cone_of_cone_comp_eval fun i => limit.cone _,
      IsLimit := cone_of_cone_eval_is_limit fun i => limit.is_limit _ }

end

section

variable [∀ i, has_colimit (F ⋙ pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ pi.eval C i`,
there is a colimit for `F`.
-/
theorem has_colimit_of_has_colimit_comp_eval : has_colimit F :=
  has_colimit.mk
    { Cocone := cocone_of_cocone_comp_eval fun i => colimit.cocone _,
      IsColimit := cocone_of_cocone_eval_is_colimit fun i => colimit.is_colimit _ }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import category_theory.limits.shapes.types`
we can use:
```
local attribute [instance] has_limit_of_has_limit_comp_eval
example : has_binary_products (I → Type v₁) := ⟨by apply_instance⟩
```
-/


end CategoryTheory.pi

