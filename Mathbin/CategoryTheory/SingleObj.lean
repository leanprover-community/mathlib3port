import Mathbin.CategoryTheory.Endomorphism 
import Mathbin.CategoryTheory.Category.Cat 
import Mathbin.Algebra.Category.Mon.Basic

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transfering some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/


universe u v w

namespace CategoryTheory

/-- Type tag on `unit` used to define single-object categories and groupoids. -/
@[nolint unused_arguments has_inhabited_instance]
def single_obj (α : Type u) : Type :=
  Unit

namespace SingleObj

variable (α : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance category_struct [HasOne α] [Mul α] : category_struct (single_obj α) :=
  { Hom := fun _ _ => α, comp := fun _ _ _ x y => y*x, id := fun _ => 1 }

/-- Monoid laws become category laws for the single object category. -/
instance category [Monoidₓ α] : category (single_obj α) :=
  { comp_id' := fun _ _ => one_mulₓ, id_comp' := fun _ _ => mul_oneₓ,
    assoc' := fun _ _ _ _ x y z => (mul_assocₓ z y x).symm }

theorem id_as_one [Monoidₓ α] (x : single_obj α) : 𝟙 x = 1 :=
  rfl

theorem comp_as_mul [Monoidₓ α] {x y z : single_obj α} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g*f :=
  rfl

/--
Groupoid structure on `single_obj α`.

See https://stacks.math.columbia.edu/tag/0019.
-/
instance groupoid [Groupₓ α] : groupoid (single_obj α) :=
  { inv := fun _ _ x => x⁻¹, inv_comp' := fun _ _ => mul_right_invₓ, comp_inv' := fun _ _ => mul_left_invₓ }

theorem inv_as_inv [Groupₓ α] {x y : single_obj α} (f : x ⟶ y) : inv f = f⁻¹ :=
  by 
    ext 
    rw [comp_as_mul, inv_mul_selfₓ, id_as_one]

/-- The single object in `single_obj α`. -/
protected def star : single_obj α :=
  Unit.star

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def to_End [Monoidₓ α] : α ≃* End (single_obj.star α) :=
  { Equiv.refl α with map_mul' := fun x y => rfl }

theorem to_End_def [Monoidₓ α] (x : α) : to_End α x = x :=
  rfl

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See https://stacks.math.columbia.edu/tag/001F --
although we do not characterize when the functor is full or faithful.
-/
def map_hom (α : Type u) (β : Type v) [Monoidₓ α] [Monoidₓ β] : (α →* β) ≃ single_obj α ⥤ single_obj β :=
  { toFun :=
      fun f =>
        { obj := id, map := fun _ _ => «expr⇑ » f, map_id' := fun _ => f.map_one,
          map_comp' := fun _ _ _ x y => f.map_mul y x },
    invFun :=
      fun f =>
        { toFun := @Functor.map _ _ _ _ f (single_obj.star α) (single_obj.star α), map_one' := f.map_id _,
          map_mul' := fun x y => f.map_comp y x },
    left_inv := fun ⟨f, h₁, h₂⟩ => rfl,
    right_inv :=
      fun f =>
        by 
          cases f <;>
            runTac 
              obviously }

theorem map_hom_id (α : Type u) [Monoidₓ α] : map_hom α α (MonoidHom.id α) = 𝟭 _ :=
  rfl

theorem map_hom_comp {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) {γ : Type w} [Monoidₓ γ]
  (g : β →* γ) : map_hom α γ (g.comp f) = map_hom α β f ⋙ map_hom β γ g :=
  rfl

/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
def difference_functor {C G} [category C] [Groupₓ G] (f : C → G) : C ⥤ single_obj G :=
  { obj := fun _ => (), map := fun x y _ => f y*f x⁻¹,
    map_id' :=
      by 
        intro 
        rw [single_obj.id_as_one, mul_right_invₓ],
    map_comp' :=
      by 
        intros 
        rw [single_obj.comp_as_mul, ←mul_assocₓ, mul_left_injₓ, mul_assocₓ, inv_mul_selfₓ, mul_oneₓ] }

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
@[reducible]
def to_functor {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) : single_obj α ⥤ single_obj β :=
  single_obj.map_hom α β f

@[simp]
theorem id_to_functor (α : Type u) [Monoidₓ α] : (id α).toFunctor = 𝟭 _ :=
  rfl

@[simp]
theorem comp_to_functor {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) {γ : Type w} [Monoidₓ γ]
  (g : β →* γ) : (g.comp f).toFunctor = f.to_functor ⋙ g.to_functor :=
  rfl

end MonoidHom

namespace Units

variable (α : Type u) [Monoidₓ α]

/--
The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def to_Aut : Units α ≃* Aut (single_obj.star α) :=
  (Units.mapEquiv (single_obj.to_End α)).trans$ Aut.units_End_equiv_Aut _

@[simp]
theorem to_Aut_hom (x : Units α) : (to_Aut α x).Hom = single_obj.to_End α x :=
  rfl

@[simp]
theorem to_Aut_inv (x : Units α) : (to_Aut α x).inv = single_obj.to_End α (x⁻¹ : Units α) :=
  rfl

end Units

namespace Mon

open CategoryTheory

/-- The fully faithful functor from `Mon` to `Cat`. -/
def to_Cat : Mon ⥤ Cat :=
  { obj := fun x => Cat.of (single_obj x), map := fun x y f => single_obj.map_hom x y f }

instance to_Cat_full : full to_Cat :=
  { Preimage := fun x y => (single_obj.map_hom x y).invFun,
    witness' :=
      fun x y =>
        by 
          apply Equiv.right_inv }

instance to_Cat_faithful : faithful to_Cat :=
  { map_injective' :=
      fun x y =>
        by 
          apply Equiv.injective }

end Mon

