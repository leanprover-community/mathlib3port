import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor 
import Mathbin.CategoryTheory.Linear.Default

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

# Implementation details

`functor.linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/


namespace CategoryTheory

variable (R : Type _) [Semiringₓ R]

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
class functor.linear {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] [linear R C] [linear R D]
  (F : C ⥤ D) [F.additive] : Prop where 
  map_smul' : ∀ {X Y : C} {f : X ⟶ Y} {r : R}, F.map (r • f) = r • F.map f :=  by 
  runTac 
    obviously

section Linear

namespace Functor

section 

variable {R} {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] (F : C ⥤ D) [Additive F] [linear R F]

@[simp]
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  functor.linear.map_smul'

instance : linear R (𝟭 C) :=
  {  }

instance {E : Type _} [category E] [preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E) [Additive G] [linear R G] :
  linear R (F ⋙ G) :=
  {  }

variable (R)

/-- `F.map_linear_map` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
def map_linear_map {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.map_add_hom with map_smul' := fun r f => F.map_smul r f }

theorem coe_map_linear_map {X Y : C} : «expr⇑ » (F.map_linear_map R : (X ⟶ Y) →ₗ[R] _) = @map C _ D _ F X Y :=
  rfl

end 

section InducedCategory

variable {C : Type _} {D : Type _} [category D] [preadditive D] [CategoryTheory.Linear R D] (F : C → D)

instance induced_functor_linear : functor.linear R (induced_functor F) :=
  {  }

end InducedCategory

section 

variable {R} {C D : Type _} [category C] [category D] [preadditive C] [preadditive D] (F : C ⥤ D) [Additive F]

instance nat_linear : F.linear ℕ :=
  { map_smul' := fun X Y f r => F.map_add_hom.map_nsmul f r }

instance int_linear : F.linear ℤ :=
  { map_smul' := fun X Y f r => F.map_add_hom.map_zsmul f r }

variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]

instance rat_linear : F.linear ℚ :=
  { map_smul' := fun X Y f r => F.map_add_hom.to_rat_linear_map.map_smul r f }

end 

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [category C] [category D] [preadditive C] [linear R C] [preadditive D] [linear R D]

instance inverse_linear (e : C ≌ D) [e.functor.additive] [e.functor.linear R] : e.inverse.linear R :=
  { map_smul' :=
      fun X Y r f =>
        by 
          apply e.functor.map_injective 
          simp  }

end Equivalenceₓ

end Linear

end CategoryTheory

