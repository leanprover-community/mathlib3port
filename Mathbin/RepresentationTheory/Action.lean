/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.SingleObj
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Monoidal.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Transport
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Abelian.FunctorCategory
import Mathbin.CategoryTheory.Abelian.Transfer

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive or abelian so is `Action V G`.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

variable (V : Type (u + 1)) [LargeCategory V]

/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
-- Note: this is _not_ a categorical action of `G` on `V`.
structure Action (G : Mon.{u}) where
  V : V
  ρ : G ⟶ Mon.of (End V)

namespace Action

variable {V}

@[simp]
theorem ρ_one {G : Mon.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V := by
  rw [MonoidHom.map_one]
  rfl

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : Groupₓₓ.{u}} (A : Action V (Mon.of G)) : G ⟶ Groupₓₓ.of (Aut A.V) where
  toFun := fun g =>
    { Hom := A.ρ g, inv := A.ρ (g⁻¹ : G),
      hom_inv_id' :=
        (A.ρ.map_mul (g⁻¹ : G) g).symm.trans
          (by
            rw [inv_mul_selfₓ, ρ_one]),
      inv_hom_id' :=
        (A.ρ.map_mul g (g⁻¹ : G)).symm.trans
          (by
            rw [mul_inv_selfₓ, ρ_one]) }
  map_one' := by
    ext
    exact A.ρ.map_one
  map_mul' := fun x y => by
    ext
    exact A.ρ.map_mul x y

variable (G : Mon.{u})

section

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroupₓₓ G where
  V := AddCommGroupₓₓ.of PUnit
  ρ := 1

instance : Inhabited (Action AddCommGroupₓₓ G) :=
  ⟨trivial G⟩

end

variable {G V}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure Hom (M N : Action V G) where
  Hom : M.V ⟶ N.V
  comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by
    run_tac
      obviously

restate_axiom hom.comm'

namespace Hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.Hom M M where
  Hom := 𝟙 M.V

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  Hom := p.Hom ≫ q.Hom
  comm' := fun g => by
    rw [← category.assoc, p.comm, category.assoc, q.comm, ← category.assoc]

end Hom

instance : Category (Action V G) where
  Hom := fun M N => Hom M N
  id := fun M => Hom.id M
  comp := fun M N K f g => Hom.comp f g

@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).Hom = 𝟙 M.V :=
  rfl

@[simp]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mkIso {M N : Action V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.Hom = f.Hom ≫ N.ρ g) : M ≅ N where
  Hom := { Hom := f.Hom, comm' := comm }
  inv :=
    { Hom := f.inv,
      comm' := fun g => by
        have w := comm g =≫ f.inv
        simp at w
        simp [w] }

namespace FunctorCategoryEquivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj := fun M =>
    { obj := fun _ => M.V, map := fun _ _ g => M.ρ g, map_id' := fun _ => M.ρ.map_one,
      map_comp' := fun _ _ _ g h => M.ρ.map_mul h g }
  map := fun M N f => { app := fun _ => f.Hom, naturality' := fun _ _ g => f.comm g }

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj := fun F =>
    { V := F.obj PUnit.unit,
      ρ := { toFun := fun g => F.map g, map_one' := F.map_id PUnit.unit, map_mul' := fun g h => F.map_comp h g } }
  map := fun M N f => { Hom := f.app PUnit.unit, comm' := fun g => f.naturality g }

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def unitIso : 𝟭 (Action V G) ≅ Functor ⋙ inverse :=
  NatIso.ofComponents
    (fun M =>
      mkIso (Iso.refl _)
        (by
          tidy))
    (by
      tidy)

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def counitIso : inverse ⋙ Functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents
    (fun M =>
      NatIso.ofComponents
        (by
          tidy)
        (by
          tidy))
    (by
      tidy)

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  Functor := Functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

attribute [simps] functor_category_equivalence

instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out := fun J _ _ => adjunction.has_limits_of_shape_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

end

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V where
  obj := fun M => M.V
  map := fun M N f => f.Hom

instance : Faithful (forget V G) where
  map_injective' := fun X Y f g w => Hom.ext _ _ w

instance [ConcreteCategory V] : ConcreteCategory (Action V G) where
  forget := forget V G ⋙ ConcreteCategory.forget V

instance hasForgetToV [ConcreteCategory V] : HasForget₂ (Action V G) V where
  forget₂ := forget V G

/-- The forgetful functor is intertwined by `functor_category_equivalence` with
evaluation at `punit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).Functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _

noncomputable instance [HasLimits V] : Limits.PreservesLimits (forget V G) :=
  Limits.preservesLimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance [HasColimits V] : PreservesColimits (forget V G) :=
  preservesColimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

section HasZeroMorphisms

variable [HasZeroMorphisms V]

instance : HasZeroMorphisms (Action V G) where
  HasZero := fun X Y =>
    ⟨⟨0, by
        tidy⟩⟩

instance : Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).Functor :=
  {  }

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance : Preadditive (Action V G) where
  homGroup := fun X Y =>
    { zero :=
        ⟨0, by
          simp ⟩,
      add := fun f g =>
        ⟨f.Hom + g.Hom, by
          simp [f.comm, g.comm]⟩,
      neg := fun f =>
        ⟨-f.Hom, by
          simp [f.comm]⟩,
      zero_add := by
        intros
        ext
        exact zero_addₓ _,
      add_zero := by
        intros
        ext
        exact add_zeroₓ _,
      add_assoc := by
        intros
        ext
        exact add_assocₓ _ _ _,
      add_left_neg := by
        intros
        ext
        exact add_left_negₓ _,
      add_comm := by
        intros
        ext
        exact add_commₓ _ _ }
  add_comp' := by
    intros
    ext
    exact preadditive.add_comp _ _ _ _ _ _
  comp_add' := by
    intros
    ext
    exact preadditive.comp_add _ _ _ _ _ _

instance : Functor.Additive (functorCategoryEquivalence V G).Functor :=
  {  }

end Preadditive

section Abelian

/-- Auxilliary construction for the `abelian (Action V G)` instance. -/
def abelianAux : Action V G ≌ ULift.{u} (SingleObj G) ⥤ V :=
  (functorCategoryEquivalence V G).trans (Equivalence.congrLeft Ulift.equivalence)

noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.Functor

end Abelian

section Monoidal

variable [MonoidalCategory V]

instance : MonoidalCategory (Action V G) :=
  Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  { Action.forget _ _ with ε := 𝟙 _, μ := fun X Y => 𝟙 _ }

instance forget_monoidal_faithful : Faithful (forgetMonoidal V G).toFunctor := by
  change faithful (forget V G)
  infer_instance

instance [BraidedCategory V] : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G)
    (fun X Y =>
      mkIso (β_ _ _)
        (by
          tidy))
    (by
      tidy)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps]
def forgetBraided [BraidedCategory V] : BraidedFunctor (Action V G) V :=
  { forgetMonoidal _ _ with }

instance forget_braided_faithful [BraidedCategory V] : Faithful (forgetBraided V G).toFunctor := by
  change faithful (forget V G)
  infer_instance

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

end Monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def actionPunitEquivalence : Action V (Mon.of PUnit) ≌ V where
  Functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩,
      map := fun X Y f =>
        ⟨f, fun ⟨⟩ => by
          simp ⟩ }
  unitIso :=
    NatIso.ofComponents
      (fun X =>
        mkIso (Iso.refl _) fun ⟨⟩ => by
          simpa using ρ_one X)
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents (fun X => Iso.refl _)
      (by
        tidy)

variable (V)

/-- The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G where
  obj := fun M => { V := M.V, ρ := f ≫ M.ρ }
  map := fun M N p => { Hom := p.Hom, comm' := fun g => p.comm (f g) }

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def resId {G : Mon} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents
    (fun M =>
      mkIso (Iso.refl _)
        (by
          tidy))
    (by
      tidy)

attribute [simps] res_id

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def resComp {G H K : Mon} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents
    (fun M =>
      mkIso (Iso.refl _)
        (by
          tidy))
    (by
      tidy)

attribute [simps] res_comp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.
end Action

namespace CategoryTheory.Functor

variable {V} {W : Type (u + 1)} [LargeCategory W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : V ⥤ W) (G : Mon.{u}) : Action V G ⥤ Action W G where
  obj := fun M =>
    { V := F.obj M.V,
      ρ :=
        { toFun := fun g => F.map (M.ρ g),
          map_one' := by
            simp only [End.one_def, Action.ρ_one, F.map_id],
          map_mul' := fun g h => by
            simp only [End.mul_def, F.map_comp, map_mul] } }
  map := fun M N f =>
    { Hom := F.map f.Hom,
      comm' := fun g => by
        dsimp'
        rw [← F.map_comp, f.comm, F.map_comp] }
  map_id' := fun M => by
    ext
    simp only [Action.id_hom, F.map_id]
  map_comp' := fun M N P f g => by
    ext
    simp only [Action.comp_hom, F.map_comp]

end CategoryTheory.Functor

