import Mathbin.CategoryTheory.Monoidal.Discrete 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal 
import Mathbin.Algebra.PunitInstances

/-!
# The category of monoids in a monoidal category.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

/--
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where 
  x : C 
  one : 𝟙_ C ⟶ X 
  mul : X ⊗ X ⟶ X 
  one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).Hom :=  by 
  runTac 
    obviously 
  mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).Hom :=  by 
  runTac 
    obviously 
  mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).Hom ≫ (𝟙 X ⊗ mul) ≫ mul :=  by 
  runTac 
    obviously

restate_axiom Mon_.one_mul'

restate_axiom Mon_.mul_one'

restate_axiom Mon_.mul_assoc'

attribute [reassoc] Mon_.one_mul Mon_.mul_one

attribute [simp, reassoc] Mon_.mul_assoc

namespace Mon_

/--
The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivialₓ : Mon_ C :=
  { x := 𝟙_ C, one := 𝟙 _, mul := (λ_ _).Hom,
    mul_assoc' :=
      by 
        simpRw [triangle_assoc, iso.cancel_iso_hom_right, tensor_right_iff, unitors_equal],
    mul_one' :=
      by 
        simp [unitors_equal] }

instance : Inhabited (Mon_ C) :=
  ⟨trivialₓ C⟩

variable {C} {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).Hom ≫ f :=
  by 
    rw [←id_tensor_comp_tensor_id, category.assoc, M.one_mul, left_unitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).Hom ≫ f :=
  by 
    rw [←tensor_id_comp_id_tensor, category.assoc, M.mul_one, right_unitor_naturality]

theorem assoc_flip : (𝟙 M.X ⊗ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ⊗ 𝟙 M.X) ≫ M.mul :=
  by 
    simp 

/-- A morphism of monoid objects. -/
@[ext]
structure hom (M N : Mon_ C) where 
  Hom : M.X ⟶ N.X 
  one_hom' : M.one ≫ hom = N.one :=  by 
  runTac 
    obviously 
  mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul :=  by 
  runTac 
    obviously

restate_axiom hom.one_hom'

restate_axiom hom.mul_hom'

attribute [simp, reassoc] hom.one_hom hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : hom M M :=
  { Hom := 𝟙 M.X }

instance hom_inhabited (M : Mon_ C) : Inhabited (hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
  { Hom := f.hom ≫ g.hom }

instance : category (Mon_ C) :=
  { Hom := fun M N => hom M N, id := id, comp := fun M N O f g => comp f g }

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : hom M M).Hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : hom M K).Hom = f.hom ≫ g.hom :=
  rfl

section 

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C :=
  { obj := fun A => A.X, map := fun A B f => f.hom }

end 

instance forget_faithful : faithful (@forget C _ _) :=
  {  }

instance {A B : Mon_ C} (f : A ⟶ B) [e : is_iso ((forget C).map f)] : is_iso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : reflects_isomorphisms (forget C) :=
  { reflects :=
      fun X Y f e =>
        by 
          exact
            ⟨⟨{ Hom := inv f.hom,
                  mul_hom' :=
                    by 
                      simp only [is_iso.comp_inv_eq, hom.mul_hom, category.assoc, ←tensor_comp_assoc, is_iso.inv_hom_id,
                        tensor_id, category.id_comp] },
                by 
                  tidy⟩⟩ }

instance unique_hom_from_trivial (A : Mon_ C) : Unique (trivialₓ C ⟶ A) :=
  { default :=
      { Hom := A.one,
        one_hom' :=
          by 
            dsimp 
            simp ,
        mul_hom' :=
          by 
            dsimp 
            simp [A.one_mul, unitors_equal] },
    uniq :=
      fun f =>
        by 
          ext 
          simp 
          rw [←category.id_comp f.hom]
          erw [f.one_hom] }

open CategoryTheory.Limits

instance : has_initial (Mon_ C) :=
  has_initial_of_unique (trivialₓ C)

end Mon_

namespace CategoryTheory.LaxMonoidalFunctor

variable {C} {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

/--
A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
@[simps]
def map_Mon (F : lax_monoidal_functor C D) : Mon_ C ⥤ Mon_ D :=
  { obj :=
      fun A =>
        { x := F.obj A.X, one := F.ε ≫ F.map A.one, mul := F.μ _ _ ≫ F.map A.mul,
          one_mul' :=
            by 
              convLHS => rw [comp_tensor_id, ←F.to_functor.map_id]
              sliceLHS 2 3 => rw [F.μ_natural]
              sliceLHS 3 4 => rw [←F.to_functor.map_comp, A.one_mul]
              rw [F.to_functor.map_id]
              rw [F.left_unitality],
          mul_one' :=
            by 
              convLHS => rw [id_tensor_comp, ←F.to_functor.map_id]
              sliceLHS 2 3 => rw [F.μ_natural]
              sliceLHS 3 4 => rw [←F.to_functor.map_comp, A.mul_one]
              rw [F.to_functor.map_id]
              rw [F.right_unitality],
          mul_assoc' :=
            by 
              convLHS => rw [comp_tensor_id, ←F.to_functor.map_id]
              sliceLHS 2 3 => rw [F.μ_natural]
              sliceLHS 3 4 => rw [←F.to_functor.map_comp, A.mul_assoc]
              convLHS => rw [F.to_functor.map_id]
              convLHS => rw [F.to_functor.map_comp, F.to_functor.map_comp]
              convRHS => rw [id_tensor_comp, ←F.to_functor.map_id]
              sliceRHS 3 4 => rw [F.μ_natural]
              convRHS => rw [F.to_functor.map_id]
              sliceRHS 1 3 => rw [←F.associativity]
              simp only [category.assoc] },
    map :=
      fun A B f =>
        { Hom := F.map f.hom,
          one_hom' :=
            by 
              dsimp 
              rw [category.assoc, ←F.to_functor.map_comp, f.one_hom],
          mul_hom' :=
            by 
              dsimp 
              rw [category.assoc, F.μ_natural_assoc, ←F.to_functor.map_comp, ←F.to_functor.map_comp, f.mul_hom] },
    map_id' :=
      fun A =>
        by 
          ext 
          simp ,
    map_comp' :=
      fun A B C f g =>
        by 
          ext 
          simp  }

variable (C D)

/-- `map_Mon` is functorial in the lax monoidal functor. -/
def map_Mon_functor : lax_monoidal_functor C D ⥤ Mon_ C ⥤ Mon_ D :=
  { obj := map_Mon, map := fun F G α => { app := fun A => { Hom := α.app A.X } } }

end CategoryTheory.LaxMonoidalFunctor

namespace Mon_

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPunit

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def lax_monoidal_to_Mon : lax_monoidal_functor (discrete PUnit.{u + 1}) C ⥤ Mon_ C :=
  { obj := fun F => (F.map_Mon : Mon_ _ ⥤ Mon_ C).obj (trivialₓ (discrete PUnit)),
    map := fun F G α => ((map_Mon_functor (discrete PUnit) C).map α).app _ }

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def Mon_to_lax_monoidal : Mon_ C ⥤ lax_monoidal_functor (discrete PUnit.{u + 1}) C :=
  { obj :=
      fun A =>
        { obj := fun _ => A.X, map := fun _ _ _ => 𝟙 _, ε := A.one, μ := fun _ _ => A.mul, map_id' := fun _ => rfl,
          map_comp' := fun _ _ _ _ _ => (category.id_comp (𝟙 A.X)).symm },
    map :=
      fun A B f =>
        { app := fun _ => f.hom,
          naturality' :=
            fun _ _ _ =>
              by 
                dsimp 
                rw [category.id_comp, category.comp_id],
          unit' := f.one_hom, tensor' := fun _ _ => f.mul_hom } }

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def unit_iso : 𝟭 (lax_monoidal_functor (discrete PUnit.{u + 1}) C) ≅ lax_monoidal_to_Mon C ⋙ Mon_to_lax_monoidal C :=
  nat_iso.of_components
    (fun F =>
      monoidal_nat_iso.of_components
        (fun _ =>
          F.to_functor.map_iso
            (eq_to_iso
              (by 
                ext)))
        (by 
          tidy)
        (by 
          tidy)
        (by 
          tidy))
    (by 
      tidy)

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def counit_iso : Mon_to_lax_monoidal C ⋙ lax_monoidal_to_Mon C ≅ 𝟭 (Mon_ C) :=
  nat_iso.of_components (fun F => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
    (by 
      tidy)

end EquivLaxMonoidalFunctorPunit

open EquivLaxMonoidalFunctorPunit

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equiv_lax_monoidal_functor_punit : lax_monoidal_functor (discrete PUnit.{u + 1}) C ≌ Mon_ C :=
  { Functor := lax_monoidal_to_Mon C, inverse := Mon_to_lax_monoidal C, unitIso := unit_iso C,
    counitIso := counit_iso C }

end Mon_

/-!
Projects:
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first, available in #3463)
* Check that `Mon_ Top ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (We've already got `Mon_ (Module R) ≌ Algebra R`, in `category_theory.monoidal.internal.Module`.)
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
* Show that if `C` is braided then `Mon_ C` is naturally monoidal.
-/


