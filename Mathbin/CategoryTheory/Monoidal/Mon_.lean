/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Discrete
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.Algebra.PunitInstances

/-!
# The category of monoids in a monoidal category.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where
  x : C
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).Hom := by
    run_tac
      obviously
  mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).Hom := by
    run_tac
      obviously
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).Hom ≫ (𝟙 X ⊗ mul) ≫ mul := by
    run_tac
      obviously

restate_axiom Mon_.one_mul'

restate_axiom Mon_.mul_one'

restate_axiom Mon_.mul_assoc'

attribute [reassoc] Mon_.one_mul Mon_.mul_one

-- We prove a more general `@[simp]` lemma below.
attribute [simp, reassoc] Mon_.mul_assoc

namespace Mon_

/-- The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivial : Mon_ C where
  x := 𝟙_ C
  one := 𝟙 _
  mul := (λ_ _).Hom
  mul_assoc' := by
    simp_rw [triangle_assoc, iso.cancel_iso_hom_right, tensor_right_iff, unitors_equal]
  mul_one' := by
    simp [unitors_equal]

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {C} {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.x) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).Hom ≫ f := by
  rw [← id_tensor_comp_tensor_id, category.assoc, M.one_mul, left_unitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.x) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).Hom ≫ f := by
  rw [← tensor_id_comp_id_tensor, category.assoc, M.mul_one, right_unitor_naturality]

theorem assoc_flip : (𝟙 M.x ⊗ M.mul) ≫ M.mul = (α_ M.x M.x M.x).inv ≫ (M.mul ⊗ 𝟙 M.x) ≫ M.mul := by
  simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon_ C) where
  Hom : M.x ⟶ N.x
  one_hom' : M.one ≫ hom = N.one := by
    run_tac
      obviously
  mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by
    run_tac
      obviously

restate_axiom hom.one_hom'

restate_axiom hom.mul_hom'

attribute [simp, reassoc] hom.one_hom hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : Hom M M where
  Hom := 𝟙 M.x

instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  Hom := f.Hom ≫ g.Hom

instance : Category (Mon_ C) where
  Hom := fun M N => Hom M N
  id := id
  comp := fun M N O f g => comp f g

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).Hom = 𝟙 M.x :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C where
  obj := fun A => A.x
  map := fun A B f => f.Hom

end

instance forget_faithful : Faithful (@forget C _ _) :=
  {  }

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.Hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : ReflectsIsomorphisms (forget C) where
  reflects := fun X Y f e =>
    ⟨⟨{ Hom := inv f.hom,
          mul_hom' := by
            simp only [is_iso.comp_inv_eq, hom.mul_hom, category.assoc, ← tensor_comp_assoc, is_iso.inv_hom_id,
              tensor_id, category.id_comp] },
        by
        tidy⟩⟩

instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
    { Hom := A.one,
      one_hom' := by
        dsimp
        simp ,
      mul_hom' := by
        dsimp
        simp [A.one_mul, unitors_equal] }
  uniq := fun f => by
    ext
    simp
    rw [← category.id_comp f.hom]
    erw [f.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon_ C) :=
  has_initial_of_unique (trivial C)

end Mon_

namespace CategoryTheory.LaxMonoidalFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
-- TODO: map_Mod F A : Mod A ⥤ Mod (F.map_Mon A)
@[simps]
def mapMon (F : LaxMonoidalFunctor C D) : Mon_ C ⥤ Mon_ D where
  obj := fun A =>
    { x := F.obj A.x, one := F.ε ≫ F.map A.one, mul := F.μ _ _ ≫ F.map A.mul,
      one_mul' := by
        conv_lhs => rw [comp_tensor_id, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.one_mul]
        rw [F.to_functor.map_id]
        rw [F.left_unitality],
      mul_one' := by
        conv_lhs => rw [id_tensor_comp, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.mul_one]
        rw [F.to_functor.map_id]
        rw [F.right_unitality],
      mul_assoc' := by
        conv_lhs => rw [comp_tensor_id, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.mul_assoc]
        conv_lhs => rw [F.to_functor.map_id]
        conv_lhs => rw [F.to_functor.map_comp, F.to_functor.map_comp]
        conv_rhs => rw [id_tensor_comp, ← F.to_functor.map_id]
        slice_rhs 3 4 => rw [F.μ_natural]
        conv_rhs => rw [F.to_functor.map_id]
        slice_rhs 1 3 => rw [← F.associativity]
        simp only [category.assoc] }
  map := fun A B f =>
    { Hom := F.map f.Hom,
      one_hom' := by
        dsimp
        rw [category.assoc, ← F.to_functor.map_comp, f.one_hom],
      mul_hom' := by
        dsimp
        rw [category.assoc, F.μ_natural_assoc, ← F.to_functor.map_comp, ← F.to_functor.map_comp, f.mul_hom] }
  map_id' := fun A => by
    ext
    simp
  map_comp' := fun A B C f g => by
    ext
    simp

variable (C D)

/-- `map_Mon` is functorial in the lax monoidal functor. -/
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D where
  obj := mapMon
  map := fun F G α => { app := fun A => { Hom := α.app A.x } }

end CategoryTheory.LaxMonoidalFunctor

namespace Mon_

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPunit

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C where
  obj := fun F => (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map := fun F G α => ((mapMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj := fun A =>
    { obj := fun _ => A.x, map := fun _ _ _ => 𝟙 _, ε := A.one, μ := fun _ _ => A.mul, map_id' := fun _ => rfl,
      map_comp' := fun _ _ _ _ _ => (Category.id_comp (𝟙 A.x)).symm }
  map := fun A B f =>
    { app := fun _ => f.Hom,
      naturality' := fun _ _ _ => by
        dsimp
        rw [category.id_comp, category.comp_id],
      unit' := f.OneHom, tensor' := fun _ _ => f.MulHom }

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def unitIso : 𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F =>
      MonoidalNatIso.ofComponents
        (fun _ =>
          F.toFunctor.mapIso
            (eqToIso
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
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents (fun F => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
    (by
      tidy)

end EquivLaxMonoidalFunctorPunit

open EquivLaxMonoidalFunctorPunit

/-- Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPunit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_ C where
  Functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

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


