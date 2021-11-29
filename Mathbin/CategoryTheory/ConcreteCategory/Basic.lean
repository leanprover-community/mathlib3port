import Mathbin.CategoryTheory.Types 
import Mathbin.CategoryTheory.EpiMono

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`,
see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/


universe w v v' u

namespace CategoryTheory

/--
A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`.

Note that `concrete_category` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class concrete_category (C : Type u) [category.{v} C] where 
  forget{} : C ⥤ Type w
  [forget_faithful : faithful forget]

attribute [instance] concrete_category.forget_faithful

/-- The forgetful functor from a concrete category to `Type u`. -/
@[reducible]
def forget (C : Type v) [category C] [concrete_category.{u} C] : C ⥤ Type u :=
  concrete_category.forget C

instance concrete_category.types : concrete_category (Type u) :=
  { forget := 𝟭 _ }

/--
Provide a coercion to `Type u` for a concrete category. This is not marked as an instance
as it could potentially apply to every type, and so is too expensive in typeclass search.

You can use it on particular examples as:
```
instance : has_coe_to_sort X := concrete_category.has_coe_to_sort X
```
-/
def concrete_category.has_coe_to_sort (C : Type v) [category C] [concrete_category C] : CoeSort C (Type u) :=
  ⟨(concrete_category.forget C).obj⟩

section 

attribute [local instance] concrete_category.has_coe_to_sort

variable {C : Type v} [category C] [concrete_category C]

@[simp]
theorem forget_obj_eq_coe {X : C} : (forget C).obj X = X :=
  rfl

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as a global instance. -/
def concrete_category.has_coe_to_fun {X Y : C} : CoeFun (X ⟶ Y) fun f => X → Y :=
  ⟨fun f => (forget _).map f⟩

attribute [local instance] concrete_category.has_coe_to_fun

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations.-/
theorem concrete_category.hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x : X, f x = g x) : f = g :=
  by 
    apply faithful.map_injective (forget C)
    ext 
    exact w x

@[simp]
theorem forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = f :=
  rfl

/--
Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_funₓ (congr_argₓ (fun k : X ⟶ Y => (k : X → Y)) h) x

theorem coe_id {X : C} : (𝟙 X : X → X) = id :=
  (forget _).map_id X

theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  (forget _).map_comp f g

@[simp]
theorem id_apply {X : C} (x : X) : (𝟙 X : X → X) x = x :=
  congr_funₓ ((forget _).map_id X) x

@[simp]
theorem comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  congr_funₓ ((forget _).map_comp _ _) x

@[simp]
theorem coe_hom_inv_id {X Y : C} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  congr_funₓ ((forget C).mapIso f).hom_inv_id x

@[simp]
theorem coe_inv_hom_id {X Y : C} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  congr_funₓ ((forget C).mapIso f).inv_hom_id y

theorem concrete_category.congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_funₓ (congr_argₓ (fun f : X ⟶ Y => (f : X → Y)) h) x

theorem concrete_category.congr_arg {X Y : C} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' :=
  congr_argₓ (f : X → Y) h

/-- In any concrete category, injective morphisms are monomorphisms. -/
theorem concrete_category.mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) : mono f :=
  faithful_reflects_mono (forget C) ((mono_iff_injective f).2 i)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
theorem concrete_category.epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : epi f :=
  faithful_reflects_epi (forget C) ((epi_iff_surjective f).2 s)

@[simp]
theorem concrete_category.has_coe_to_fun_Type {X Y : Type u} (f : X ⟶ Y) : coeFn f = f :=
  rfl

end 

/--
`has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class has_forget₂ (C : Type v) (D : Type v') [category C] [concrete_category.{u} C] [category D]
  [concrete_category.{u} D] where 
  forget₂ : C ⥤ D 
  forget_comp : forget₂ ⋙ forget D = forget C :=  by 
  runTac 
    obviously

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget₂ C `. -/
@[reducible]
def forget₂ (C : Type v) (D : Type v') [category C] [concrete_category C] [category D] [concrete_category D]
  [has_forget₂ C D] : C ⥤ D :=
  has_forget₂.forget₂

instance forget_faithful (C : Type v) (D : Type v') [category C] [concrete_category C] [category D]
  [concrete_category D] [has_forget₂ C D] : faithful (forget₂ C D) :=
  has_forget₂.forget_comp.faithful_of_comp

instance induced_category.concrete_category {C : Type v} {D : Type v'} [category D] [concrete_category D] (f : C → D) :
  concrete_category (induced_category D f) :=
  { forget := induced_functor f ⋙ forget D }

instance induced_category.has_forget₂ {C : Type v} {D : Type v'} [category D] [concrete_category D] (f : C → D) :
  has_forget₂ (induced_category D f) D :=
  { forget₂ := induced_functor f, forget_comp := rfl }

/--
In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def has_forget₂.mk' {C : Type v} {D : Type v'} [category C] [concrete_category C] [category D] [concrete_category D]
  (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq ((forget D).map (map f)) ((forget C).map f)) : has_forget₂ C D :=
  { forget₂ := faithful.div _ _ _ @h_obj _ @h_map,
    forget_comp :=
      by 
        apply faithful.div_comp }

instance has_forget_to_Type (C : Type v) [category C] [concrete_category C] : has_forget₂ C (Type u) :=
  { forget₂ := forget C, forget_comp := functor.comp_id _ }

end CategoryTheory

