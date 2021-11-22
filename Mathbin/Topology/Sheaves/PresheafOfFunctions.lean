import Mathbin.CategoryTheory.Yoneda 
import Mathbin.Topology.Sheaves.Presheaf 
import Mathbin.Topology.Category.TopCommRing 
import Mathbin.Topology.ContinuousFunction.Algebra

/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheaf_to_Types X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheaf_to_Type X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheaf_to_Top X T`, where `T : Top`,
  is the presheaf of continuous functions into a topological space `T`
* `presheaf_To_TopCommRing X R`, where `R : TopCommRing`
  is the presheaf valued in `CommRing` of functions functions into a topological ring `R`
* as an example of the previous construction,
  `presheaf_to_TopCommRing X (TopCommRing.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/


universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

namespace Top

variable(X : Top.{v})

/--
The presheaf of dependently typed functions on `X`, with fibres given by a type family `T`.
There is no requirement that the functions are continuous, here.
-/
def presheaf_to_Types (T : X → Type v) : X.presheaf (Type v) :=
  { obj := fun U => ∀ x : unop U, T x, map := fun U V i g => fun x : unop V => g (i.unop x) }

@[simp]
theorem presheaf_to_Types_obj {T : X → Type v} {U : «expr ᵒᵖ» (opens X)} :
  (presheaf_to_Types X T).obj U = ∀ x : unop U, T x :=
  rfl

@[simp]
theorem presheaf_to_Types_map {T : X → Type v} {U V : «expr ᵒᵖ» (opens X)} {i : U ⟶ V} {f} :
  (presheaf_to_Types X T).map i f = fun x => f (i.unop x) :=
  rfl

/--
The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
def presheaf_to_Type (T : Type v) : X.presheaf (Type v) :=
  { obj := fun U => unop U → T, map := fun U V i g => g ∘ i.unop }

@[simp]
theorem presheaf_to_Type_obj {T : Type v} {U : «expr ᵒᵖ» (opens X)} : (presheaf_to_Type X T).obj U = (unop U → T) :=
  rfl

@[simp]
theorem presheaf_to_Type_map {T : Type v} {U V : «expr ᵒᵖ» (opens X)} {i : U ⟶ V} {f} :
  (presheaf_to_Type X T).map i f = (f ∘ i.unop) :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space
`T`. -/
def presheaf_to_Top (T : Top.{v}) : X.presheaf (Type v) :=
  (opens.to_Top X).op ⋙ yoneda.obj T

@[simp]
theorem presheaf_to_Top_obj (T : Top.{v}) (U : «expr ᵒᵖ» (opens X)) :
  (presheaf_to_Top X T).obj U = ((opens.to_Top X).obj (unop U) ⟶ T) :=
  rfl

/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
def continuous_functions (X : «expr ᵒᵖ» Top.{v}) (R : TopCommRing.{v}) : CommRingₓₓ.{v} :=
  CommRingₓₓ.of (unop X ⟶ (forget₂ TopCommRing Top).obj R)

namespace ContinuousFunctions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : «expr ᵒᵖ» Top} (f : X ⟶ Y) (R : TopCommRing) :
  continuous_functions X R ⟶ continuous_functions Y R :=
  { toFun := fun g => f.unop ≫ g, map_one' := rfl, map_zero' := rfl,
    map_add' :=
      by 
        tidy,
    map_mul' :=
      by 
        tidy }

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : «expr ᵒᵖ» Top.{u}) {R S : TopCommRing.{u}} (φ : R ⟶ S) :
  continuous_functions X R ⟶ continuous_functions X S :=
  { toFun := fun g => g ≫ (forget₂ TopCommRing Top).map φ,
    map_one' :=
      by 
        ext <;> exact φ.1.map_one,
    map_zero' :=
      by 
        ext <;> exact φ.1.map_zero,
    map_add' :=
      by 
        intros  <;> ext <;> apply φ.1.map_add,
    map_mul' :=
      by 
        intros  <;> ext <;> apply φ.1.map_mul }

end ContinuousFunctions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : Top` to `R : TopCommRing` form a commutative ring, functorial in both `X` and `R`. -/
def CommRing_yoneda : TopCommRing.{u} ⥤ «expr ᵒᵖ» Top.{u} ⥤ CommRingₓₓ.{u} :=
  { obj := fun R => { obj := fun X => continuous_functions X R, map := fun X Y f => continuous_functions.pullback f R },
    map := fun R S φ => { app := fun X => continuous_functions.map X φ } }

/--
The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex valued functions of `X` as
```
presheaf_to_TopCommRing X (TopCommRing.of ℂ)
```
(this requires `import topology.instances.complex`).
-/
def presheaf_to_TopCommRing (T : TopCommRing.{v}) : X.presheaf CommRingₓₓ.{v} :=
  (opens.to_Top X).op ⋙ CommRing_yoneda.obj T

end Top

