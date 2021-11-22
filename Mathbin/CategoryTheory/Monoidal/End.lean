import Mathbin.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/


universe v u

namespace CategoryTheory

variable(C : Type u)[category.{v} C]

/--
The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctor_monoidal_category : monoidal_category (C ⥤ C) :=
  { tensorObj := fun F G => F ⋙ G, tensorHom := fun F G F' G' α β => α ◫ β, tensorUnit := 𝟭 C,
    associator := fun F G H => functor.associator F G H, leftUnitor := fun F => functor.left_unitor F,
    rightUnitor := fun F => functor.right_unitor F }

open CategoryTheory.MonoidalCategory

variable[monoidal_category.{v} C]

attribute [local instance] endofunctor_monoidal_category

attribute [local reducible] endofunctor_monoidal_category

/--
Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simps]
def tensoring_right_monoidal : monoidal_functor C (C ⥤ C) :=
  { tensoring_right C with ε := (right_unitor_nat_iso C).inv,
    μ :=
      fun X Y =>
        { app := fun Z => (α_ Z X Y).Hom,
          naturality' :=
            fun Z Z' f =>
              by 
                dsimp 
                rw [associator_naturality]
                simp  },
    μ_natural' :=
      fun X Y X' Y' f g =>
        by 
          ext Z 
          dsimp 
          simp [associator_naturality],
    associativity' :=
      fun X Y Z =>
        by 
          ext W 
          dsimp 
          simp [pentagon],
    left_unitality' :=
      fun X =>
        by 
          ext Y 
          dsimp 
          rw [category.id_comp, triangle, ←tensor_comp]
          simp ,
    right_unitality' :=
      fun X =>
        by 
          ext Y 
          dsimp 
          rw [tensor_id, category.comp_id, right_unitor_tensor_inv, category.assoc, iso.inv_hom_id_assoc,
            ←id_tensor_comp, iso.inv_hom_id, tensor_id],
    ε_is_iso :=
      by 
        infer_instance,
    μ_is_iso :=
      fun X Y =>
        ⟨⟨{ app := fun Z => (α_ Z X Y).inv,
              naturality' :=
                fun Z Z' f =>
                  by 
                    dsimp 
                    rw [←associator_inv_naturality]
                    simp  },
            by 
              tidy⟩⟩ }

end CategoryTheory

