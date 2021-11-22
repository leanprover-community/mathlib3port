import Mathbin.CategoryTheory.Monoidal.Braided 
import Mathbin.CategoryTheory.Monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable(C : Type u₁)[category.{v₁} C][monoidal_category.{v₁} C][braided_category.{v₁} C]

/--
A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ extends Mon_ C where 
  mul_comm' : (β_ _ _).Hom ≫ mul = mul :=  by 
  runTac 
    obviously

restate_axiom CommMon_.mul_comm'

attribute [simp, reassoc] CommMon_.mul_comm

namespace CommMon_

/--
The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
@[simps]
def trivialₓ : CommMon_ C :=
  { Mon_.trivial C with
    mul_comm' :=
      by 
        dsimp 
        rw [braiding_left_unitor, unitors_equal] }

instance  : Inhabited (CommMon_ C) :=
  ⟨trivialₓ C⟩

variable{C}{M : CommMon_ C}

instance  : category (CommMon_ C) :=
  induced_category.category CommMon_.toMon_

@[simp]
theorem id_hom (A : CommMon_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) : Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

section 

variable(C)

-- error in CategoryTheory.Monoidal.CommMon_: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler full
/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[derive #["[", expr full, ",", expr faithful, "]"]]
def forget₂_Mon_ : «expr ⥤ »(CommMon_ C, Mon_ C) :=
induced_functor CommMon_.to_Mon_

@[simp]
theorem forget₂_Mon_obj_one (A : CommMon_ C) : ((forget₂_Mon_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂_Mon_obj_mul (A : CommMon_ C) : ((forget₂_Mon_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂_Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂_Mon_ C).map f).Hom = f.hom :=
  rfl

end 

instance unique_hom_from_trivial (A : CommMon_ C) : Unique (trivialₓ C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.to_Mon_

open CategoryTheory.Limits

instance  : has_initial (CommMon_ C) :=
  has_initial_of_unique (trivialₓ C)

end CommMon_

namespace CategoryTheory.LaxBraidedFunctor

variable{C}{D : Type u₂}[category.{v₂} D][monoidal_category.{v₂} D][braided_category.{v₂} D]

/--
A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps]
def map_CommMon (F : lax_braided_functor C D) : CommMon_ C ⥤ CommMon_ D :=
  { obj :=
      fun A =>
        { F.to_lax_monoidal_functor.map_Mon.obj A.to_Mon_ with
          mul_comm' :=
            by 
              dsimp 
              have  := F.braided 
              sliceLHS 1 2 => rw [←this]
              sliceLHS 2 3 => rw [←CategoryTheory.Functor.map_comp, A.mul_comm] },
    map := fun A B f => F.to_lax_monoidal_functor.map_Mon.map f }

variable(C)(D)

/-- `map_CommMon` is functorial in the lax braided functor. -/
def map_CommMon_functor : lax_braided_functor C D ⥤ CommMon_ C ⥤ CommMon_ D :=
  { obj := map_CommMon, map := fun F G α => { app := fun A => { Hom := α.app A.X } } }

end CategoryTheory.LaxBraidedFunctor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPunit

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def lax_braided_to_CommMon : lax_braided_functor (discrete PUnit.{u + 1}) C ⥤ CommMon_ C :=
  { obj := fun F => (F.map_CommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivialₓ (discrete PUnit)),
    map := fun F G α => ((map_CommMon_functor (discrete PUnit) C).map α).app _ }

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def CommMon_to_lax_braided : CommMon_ C ⥤ lax_braided_functor (discrete PUnit.{u + 1}) C :=
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

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def unit_iso :
  𝟭 (lax_braided_functor (discrete PUnit.{u + 1}) C) ≅ lax_braided_to_CommMon C ⋙ CommMon_to_lax_braided C :=
  nat_iso.of_components
    (fun F =>
      lax_braided_functor.mk_iso
        (monoidal_nat_iso.of_components
          (fun _ =>
            F.to_lax_monoidal_functor.to_functor.map_iso
              (eq_to_iso
                (by 
                  ext)))
          (by 
            tidy)
          (by 
            tidy)
          (by 
            tidy)))
    (by 
      tidy)

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def counit_iso : CommMon_to_lax_braided C ⋙ lax_braided_to_CommMon C ≅ 𝟭 (CommMon_ C) :=
  nat_iso.of_components (fun F => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
    (by 
      tidy)

end EquivLaxBraidedFunctorPunit

open EquivLaxBraidedFunctorPunit

/--
Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equiv_lax_braided_functor_punit : lax_braided_functor (discrete PUnit.{u + 1}) C ≌ CommMon_ C :=
  { Functor := lax_braided_to_CommMon C, inverse := CommMon_to_lax_braided C, unitIso := unit_iso C,
    counitIso := counit_iso C }

end CommMon_

