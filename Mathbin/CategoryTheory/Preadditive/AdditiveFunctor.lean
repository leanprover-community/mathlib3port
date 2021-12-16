import Mathbin.CategoryTheory.Preadditive.Default 
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Project:

- Prove that a functor is additive if it preserves finite biproducts
  (See https://stacks.math.columbia.edu/tag/010M.)
-/


namespace CategoryTheory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] (F : C ⥤ D) : Prop where 
  map_add' : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f+g) = F.map f+F.map g :=  by 
  runTac 
    obviously

section Preadditive

namespace Functor

section 

variable {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] (F : C ⥤ D) [functor.additive F]

@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f+g) = F.map f+F.map g :=
  functor.additive.map_add'

/-- `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps (config := { fullyApplied := ff })]
def map_add_hom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun f g => F.map_add

theorem coe_map_add_hom {X Y : C} : ⇑(F.map_add_hom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y :=
  rfl

@[simp]
theorem map_zero {X Y : C} : F.map (0 : X ⟶ Y) = 0 :=
  F.map_add_hom.map_zero

instance : Additive (𝟭 C) :=
  {  }

instance {E : Type _} [category E] [preadditive E] (G : D ⥤ E) [functor.additive G] : Additive (F ⋙ G) :=
  {  }

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  F.map_add_hom.map_neg _

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  F.map_add_hom.map_sub _ _

theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  F.map_add_hom.map_zsmul _ _

open_locale BigOperators

@[simp]
theorem map_sum {X Y : C} {α : Type _} (f : α → (X ⟶ Y)) (s : Finset α) :
  F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  (F.map_add_hom : (X ⟶ Y) →+ _).map_sum f s

open CategoryTheory.Limits

open_locale ZeroObject

/-- An additive functor takes the zero object to the zero object (up to isomorphism). -/
@[simps]
def map_zero_object [has_zero_object C] [has_zero_object D] : F.obj 0 ≅ 0 :=
  { Hom := 0, inv := 0,
    hom_inv_id' :=
      by 
        rw [←F.map_id]
        simp  }

end 

section InducedCategory

variable {C : Type _} {D : Type _} [category D] [preadditive D] (F : C → D)

instance induced_functor_additive : functor.additive (induced_functor F) :=
  {  }

end InducedCategory

section 

noncomputable section 

universe v u₁ u₂

variable {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D] [preadditive C] [preadditive D] (F : C ⥤ D)
  [functor.additive F]

open CategoryTheory.Limits

/--
An additive functor between preadditive categories creates finite biproducts.
-/
instance map_has_biproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [has_biproduct f] :
  has_biproduct fun j => F.obj (f j) :=
  has_biproduct_of_total
    { x := F.obj (⨁ f), π := fun j => F.map (biproduct.π f j), ι := fun j => F.map (biproduct.ι f j),
      ι_π :=
        fun j j' =>
          by 
            simp only [←F.map_comp]
            splitIfs
            ·
              subst h 
              simp 
            ·
              simp [h] }
    (by 
      simpRw [←F.map_comp, ←F.map_sum, biproduct.total, Functor.map_id])

/--
An additive functor between preadditive categories preserves finite biproducts.
-/
@[simps]
def map_biproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [has_biproduct f] :
  F.obj (⨁ f) ≅ ⨁ fun j => F.obj (f j) :=
  { Hom := biproduct.lift fun j => F.map (biproduct.π f j), inv := biproduct.desc fun j => F.map (biproduct.ι f j),
    hom_inv_id' :=
      by 
        simp only [biproduct.lift_desc, ←F.map_comp, ←F.map_sum, biproduct.total, F.map_id],
    inv_hom_id' :=
      by 
        ext j j' 
        simp only [category.comp_id, category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, ←F.map_comp,
          biproduct.ι_π, F.map_dite, dif_ctx_congr, eq_to_hom_map, F.map_zero] }

end 

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [category C] [category D] [preadditive C] [preadditive D]

instance inverse_additive (e : C ≌ D) [e.functor.additive] : e.inverse.additive :=
  { map_add' :=
      fun X Y f g =>
        by 
          apply e.functor.map_injective 
          simp  }

end Equivalenceₓ

end Preadditive

end CategoryTheory

