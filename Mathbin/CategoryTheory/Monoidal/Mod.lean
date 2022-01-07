import Mathbin.CategoryTheory.Monoidal.Mon_

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

variable {C}

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Modₓ (A : Mon_ C) where
  x : C
  act : A.X ⊗ X ⟶ X
  one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).Hom := by
    run_tac
      obviously
  assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.X A.X X).Hom ≫ (𝟙 A.X ⊗ act) ≫ act := by
    run_tac
      obviously

restate_axiom Modₓ.one_act'

restate_axiom Modₓ.assoc'

attribute [simp, reassoc] Modₓ.one_act Modₓ.assoc

namespace Modₓ

variable {A : Mon_ C} (M : Modₓ A)

theorem assoc_flip : (𝟙 A.X ⊗ M.act) ≫ M.act = (α_ A.X A.X M.X).inv ≫ (A.mul ⊗ 𝟙 M.X) ≫ M.act := by
  simp

/-- A morphism of module objects. -/
@[ext]
structure hom (M N : Modₓ A) where
  Hom : M.X ⟶ N.X
  act_hom' : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act := by
    run_tac
      obviously

restate_axiom hom.act_hom'

attribute [simp, reassoc] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Modₓ A) : hom M M where
  Hom := 𝟙 M.X

instance hom_inhabited (M : Modₓ A) : Inhabited (hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Modₓ A} (f : hom M N) (g : hom N O) : hom M O where
  Hom := f.hom ≫ g.hom

instance : category (Modₓ A) where
  Hom := fun M N => hom M N
  id := id
  comp := fun M N O f g => comp f g

@[simp]
theorem id_hom' (M : Modₓ A) : (𝟙 M : hom M M).Hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Modₓ A} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : hom M K).Hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Modₓ A where
  x := A.X
  act := A.mul

instance : Inhabited (Modₓ A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Modₓ A ⥤ C where
  obj := fun A => A.X
  map := fun A B f => f.hom

open CategoryTheory.MonoidalCategory

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Modₓ B ⥤ Modₓ A where
  obj := fun M =>
    { x := M.X, act := (f.hom ⊗ 𝟙 M.X) ≫ M.act,
      one_act' := by
        slice_lhs 1 2 => rw [← comp_tensor_id]
        rw [f.one_hom, one_act],
      assoc' := by
        slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        rw [id_tensor_comp]
        slice_rhs 4 5 => rw [Modₓ.assoc_flip]
        slice_rhs 3 4 => rw [associator_inv_naturality]
        slice_rhs 2 3 => rw [← tensor_id, associator_inv_naturality]
        slice_rhs 1 3 => rw [iso.hom_inv_id_assoc]
        slice_rhs 1 2 => rw [← comp_tensor_id, tensor_id_comp_id_tensor]
        slice_rhs 1 2 => rw [← comp_tensor_id, ← f.mul_hom]
        rw [comp_tensor_id, category.assoc] }
  map := fun M N g =>
    { Hom := g.hom,
      act_hom' := by
        dsimp
        slice_rhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        slice_rhs 2 3 => rw [← g.act_hom]
        rw [category.assoc] }

end Modₓ

