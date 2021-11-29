import Mathbin.CategoryTheory.Monoidal.NaturalTransformation 
import Mathbin.CategoryTheory.Monoidal.Discrete

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `braided_monoidal_category` another typeclass, but then have `symmetric_monoidal_category`
extend this. The rationale is that we are not carrying any additional data,
just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

-/


open CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

/--
A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class braided_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] where 
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X 
  braiding_naturality' :
  ∀ {X X' Y Y' : C} f : X ⟶ Y g : X' ⟶ Y', (f ⊗ g) ≫ (braiding Y Y').Hom = (braiding X X').Hom ≫ (g ⊗ f) :=  by 
  runTac 
    obviously 
  hexagon_forward' :
  ∀ X Y Z : C,
    (α_ X Y Z).Hom ≫ (braiding X (Y ⊗ Z)).Hom ≫ (α_ Y Z X).Hom =
      ((braiding X Y).Hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).Hom ≫ (𝟙 Y ⊗ (braiding X Z).Hom) :=
   by 
  runTac 
    obviously 
  hexagon_reverse' :
  ∀ X Y Z : C,
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).Hom ≫ (α_ Z X Y).inv =
      (𝟙 X ⊗ (braiding Y Z).Hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).Hom ⊗ 𝟙 Y) :=
   by 
  runTac 
    obviously

restate_axiom braided_category.braiding_naturality'

attribute [simp, reassoc] braided_category.braiding_naturality

restate_axiom braided_category.hexagon_forward'

restate_axiom braided_category.hexagon_reverse'

open Category

open MonoidalCategory

open BraidedCategory

notation "β_" => braiding

section 

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/


variable (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]

theorem braiding_left_unitor_aux₁ (X : C) :
  (α_ (𝟙_ C) (𝟙_ C) X).Hom ≫ (𝟙 _ ⊗ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).Hom ⊗ 𝟙 _) =
    ((λ_ _).Hom ⊗ 𝟙 X) ≫ (β_ X _).inv :=
  by 
    rw [←left_unitor_tensor, left_unitor_naturality]
    simp 

theorem braiding_left_unitor_aux₂ (X : C) :
  ((β_ X (𝟙_ C)).Hom ⊗ 𝟙 (𝟙_ C)) ≫ ((λ_ X).Hom ⊗ 𝟙 (𝟙_ C)) = (ρ_ X).Hom ⊗ 𝟙 (𝟙_ C) :=
  calc
    ((β_ X (𝟙_ C)).Hom ⊗ 𝟙 (𝟙_ C)) ≫ ((λ_ X).Hom ⊗ 𝟙 (𝟙_ C)) =
      ((β_ X (𝟙_ C)).Hom ⊗ 𝟙 (𝟙_ C)) ≫ (α_ _ _ _).Hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).Hom ⊗ 𝟙 (𝟙_ C)) :=
    by 
      simp 
    _ =
      ((β_ X (𝟙_ C)).Hom ⊗ 𝟙 (𝟙_ C)) ≫
        (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ (β_ X _).Hom) ≫ (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).Hom ⊗ 𝟙 (𝟙_ C)) :=
    by 
      sliceRHS 3 4 => rw [←id_tensor_comp, iso.hom_inv_id, tensor_id]
      rw [id_comp]
    _ =
      (α_ _ _ _).Hom ≫
        (β_ _ _).Hom ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).Hom ⊗ 𝟙 (𝟙_ C)) :=
    by 
      sliceLHS 1 3 => rw [←hexagon_forward]
      simp only [assoc]
    _ = (α_ _ _ _).Hom ≫ (β_ _ _).Hom ≫ ((λ_ _).Hom ⊗ 𝟙 X) ≫ (β_ X _).inv :=
    by 
      rw [braiding_left_unitor_aux₁]
    _ = (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ (λ_ _).Hom) ≫ (β_ _ _).Hom ≫ (β_ X _).inv :=
    by 
      sliceLHS 2 3 => rw [←braiding_naturality]
      simp only [assoc]
    _ = (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ (λ_ _).Hom) :=
    by 
      rw [iso.hom_inv_id, comp_id]
    _ = (ρ_ X).Hom ⊗ 𝟙 (𝟙_ C) :=
    by 
      rw [triangle]
    

@[simp]
theorem braiding_left_unitor (X : C) : (β_ X (𝟙_ C)).Hom ≫ (λ_ X).Hom = (ρ_ X).Hom :=
  by 
    rw [←tensor_right_iff, comp_tensor_id, braiding_left_unitor_aux₂]

theorem braiding_right_unitor_aux₁ (X : C) :
  (α_ X (𝟙_ C) (𝟙_ C)).inv ≫ ((β_ (𝟙_ C) X).inv ⊗ 𝟙 _) ≫ (α_ _ X _).Hom ≫ (𝟙 _ ⊗ (ρ_ X).Hom) =
    (𝟙 X ⊗ (ρ_ _).Hom) ≫ (β_ _ X).inv :=
  by 
    rw [←right_unitor_tensor, right_unitor_naturality]
    simp 

theorem braiding_right_unitor_aux₂ (X : C) :
  (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).Hom) ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).Hom) = 𝟙 (𝟙_ C) ⊗ (λ_ X).Hom :=
  calc
    (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).Hom) ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).Hom) =
      (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).Hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).Hom ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).Hom) :=
    by 
      simp 
    _ =
      (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).Hom) ≫
        (α_ _ _ _).inv ≫ ((β_ _ X).Hom ⊗ 𝟙 _) ≫ ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).Hom) :=
    by 
      sliceRHS 3 4 => rw [←comp_tensor_id, iso.hom_inv_id, tensor_id]
      rw [id_comp]
    _ =
      (α_ _ _ _).inv ≫
        (β_ _ _).Hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).Hom) :=
    by 
      sliceLHS 1 3 => rw [←hexagon_reverse]
      simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).Hom ≫ (𝟙 X ⊗ (ρ_ _).Hom) ≫ (β_ _ X).inv :=
    by 
      rw [braiding_right_unitor_aux₁]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).Hom ⊗ 𝟙 _) ≫ (β_ _ X).Hom ≫ (β_ _ _).inv :=
    by 
      sliceLHS 2 3 => rw [←braiding_naturality]
      simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).Hom ⊗ 𝟙 _) :=
    by 
      rw [iso.hom_inv_id, comp_id]
    _ = 𝟙 (𝟙_ C) ⊗ (λ_ X).Hom :=
    by 
      rw [triangle_assoc_comp_right]
    

@[simp]
theorem braiding_right_unitor (X : C) : (β_ (𝟙_ C) X).Hom ≫ (ρ_ X).Hom = (λ_ X).Hom :=
  by 
    rw [←tensor_left_iff, id_tensor_comp, braiding_right_unitor_aux₂]

end 

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.

See https://stacks.math.columbia.edu/tag/0FFW.
-/
class symmetric_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] extends braided_category.{v} C where 
  symmetry' : ∀ X Y : C, (β_ X Y).Hom ≫ (β_ Y X).Hom = 𝟙 (X ⊗ Y) :=  by 
  runTac 
    obviously

restate_axiom symmetric_category.symmetry'

attribute [simp, reassoc] symmetric_category.symmetry

variable (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]

variable (D : Type u₂) [category.{v₂} D] [monoidal_category D] [braided_category D]

variable (E : Type u₃) [category.{v₃} E] [monoidal_category E] [braided_category E]

/--
A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
structure lax_braided_functor extends lax_monoidal_functor C D where 
  braided' : ∀ X Y : C, μ X Y ≫ map (β_ X Y).Hom = (β_ (obj X) (obj Y)).Hom ≫ μ Y X :=  by 
  runTac 
    obviously

restate_axiom lax_braided_functor.braided'

namespace LaxBraidedFunctor

/-- The identity lax braided monoidal functor. -/
@[simps]
def id : lax_braided_functor C C :=
  { monoidal_functor.id C with  }

instance : Inhabited (lax_braided_functor C C) :=
  ⟨id C⟩

variable {C D E}

/-- The composition of lax braided monoidal functors. -/
@[simps]
def comp (F : lax_braided_functor C D) (G : lax_braided_functor D E) : lax_braided_functor C E :=
  { lax_monoidal_functor.comp F.to_lax_monoidal_functor G.to_lax_monoidal_functor with
    braided' :=
      fun X Y =>
        by 
          dsimp 
          sliceLHS 2 3 => rw [←CategoryTheory.Functor.map_comp, F.braided, CategoryTheory.Functor.map_comp]
          sliceLHS 1 2 => rw [G.braided]
          simp only [category.assoc] }

instance category_lax_braided_functor : category (lax_braided_functor C D) :=
  induced_category.category lax_braided_functor.to_lax_monoidal_functor

@[simp]
theorem comp_to_nat_trans {F G H : lax_braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).toNatTrans = @category_struct.comp (C ⥤ D) _ _ _ _ α.to_nat_trans β.to_nat_trans :=
  rfl

/--
Interpret a natural isomorphism of the underlyling lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simps]
def mk_iso {F G : lax_braided_functor C D} (i : F.to_lax_monoidal_functor ≅ G.to_lax_monoidal_functor) : F ≅ G :=
  { i with  }

end LaxBraidedFunctor

/--
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
structure braided_functor extends monoidal_functor C D where 
  braided' : ∀ X Y : C, map (β_ X Y).Hom = inv (μ X Y) ≫ (β_ (obj X) (obj Y)).Hom ≫ μ Y X :=  by 
  runTac 
    obviously

restate_axiom braided_functor.braided'

attribute [simp] braided_functor.braided

namespace BraidedFunctor

/-- Turn a braided functor into a lax braided functor. -/
@[simps]
def to_lax_braided_functor (F : braided_functor C D) : lax_braided_functor C D :=
  { F with
    braided' :=
      fun X Y =>
        by 
          rw [F.braided]
          simp  }

/-- The identity braided monoidal functor. -/
@[simps]
def id : braided_functor C C :=
  { monoidal_functor.id C with  }

instance : Inhabited (braided_functor C C) :=
  ⟨id C⟩

variable {C D E}

/-- The composition of braided monoidal functors. -/
@[simps]
def comp (F : braided_functor C D) (G : braided_functor D E) : braided_functor C E :=
  { monoidal_functor.comp F.to_monoidal_functor G.to_monoidal_functor with  }

instance category_braided_functor : category (braided_functor C D) :=
  induced_category.category braided_functor.to_monoidal_functor

@[simp]
theorem comp_to_nat_trans {F G H : braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).toNatTrans = @category_struct.comp (C ⥤ D) _ _ _ _ α.to_nat_trans β.to_nat_trans :=
  rfl

/--
Interpret a natural isomorphism of the underlyling monoidal functors as an
isomorphism of the braided monoidal functors.
-/
@[simps]
def mk_iso {F G : braided_functor C D} (i : F.to_monoidal_functor ≅ G.to_monoidal_functor) : F ≅ G :=
  { i with  }

end BraidedFunctor

section CommMonoidₓ

variable (M : Type u) [CommMonoidₓ M]

instance comm_monoid_discrete : CommMonoidₓ (discrete M) :=
  by 
    dsimp [discrete]
    infer_instance

instance : braided_category (discrete M) :=
  { braiding := fun X Y => eq_to_iso (mul_commₓ X Y) }

variable {M} {N : Type u} [CommMonoidₓ N]

/--
A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
@[simps]
def discrete.braided_functor (F : M →* N) : braided_functor (discrete M) (discrete N) :=
  { discrete.monoidal_functor F with  }

end CommMonoidₓ

end CategoryTheory

