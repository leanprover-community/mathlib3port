import Mathbin.CategoryTheory.FullSubcategory

/-!
# Groupoids

We define `groupoid` as a typeclass extending `category`,
asserting that all morphisms have inverses.

The instance `is_iso.of_groupoid (f : X ⟶ Y) : is_iso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `groupoid.of_is_iso` from an existing category
with `is_iso f` for every `f`.

## See also

See also `category_theory.core` for the groupoid of isomorphisms in a category.
-/


namespace CategoryTheory

universe v v₂ u u₂

/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
class groupoid(obj : Type u) extends category.{v} obj : Type max u (v + 1) where 
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  inv_comp' : ∀ {X Y : obj} f : X ⟶ Y, comp (inv f) f = id Y :=  by 
  runTac 
    obviously 
  comp_inv' : ∀ {X Y : obj} f : X ⟶ Y, comp f (inv f) = id X :=  by 
  runTac 
    obviously

restate_axiom groupoid.inv_comp'

restate_axiom groupoid.comp_inv'

attribute [simp] groupoid.inv_comp groupoid.comp_inv

/--
A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev large_groupoid (C : Type (u + 1)) : Type (u + 1) :=
  groupoid.{u} C

/--
A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev small_groupoid (C : Type u) : Type (u + 1) :=
  groupoid.{u} C

section 

variable{C : Type u}[groupoid.{v} C]{X Y : C}

instance (priority := 100)is_iso.of_groupoid (f : X ⟶ Y) : is_iso f :=
  ⟨⟨groupoid.inv f,
      by 
        simp ⟩⟩

variable(X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y) :=
  { toFun := iso.hom, invFun := fun f => ⟨f, groupoid.inv f⟩, left_inv := fun i => iso.ext rfl,
    right_inv := fun f => rfl }

end 

section 

variable{C : Type u}[category.{v} C]

/-- A category where every morphism `is_iso` is a groupoid. -/
noncomputable def groupoid.of_is_iso (all_is_iso : ∀ {X Y : C} f : X ⟶ Y, is_iso f) : groupoid.{v} C :=
  { inv := fun X Y f => inv f }

end 

instance induced_category.groupoid {C : Type u} (D : Type u₂) [groupoid.{v} D] (F : C → D) :
  groupoid.{v} (induced_category D F) :=
  { induced_category.category F with inv := fun X Y f => groupoid.inv f, inv_comp' := fun X Y f => groupoid.inv_comp f,
    comp_inv' := fun X Y f => groupoid.comp_inv f }

end CategoryTheory

