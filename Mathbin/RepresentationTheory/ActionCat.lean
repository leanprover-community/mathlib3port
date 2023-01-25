/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module representation_theory.Action
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.GroupCat.Basic
import Mathbin.CategoryTheory.SingleObj
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Monoidal.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Transport
import Mathbin.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathbin.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Linear
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Abelian.FunctorCategory
import Mathbin.CategoryTheory.Abelian.Transfer
import Mathbin.CategoryTheory.Conj
import Mathbin.CategoryTheory.Linear.FunctorCategory

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

variable (V : Type (u + 1)) [LargeCategory V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
structure ActionCat (G : MonCat.{u}) where
  V : V
  ρ : G ⟶ MonCat.of (EndCat V)
#align Action ActionCat

namespace ActionCat

variable {V}

@[simp]
theorem ρ_one {G : MonCat.{u}} (A : ActionCat V G) : A.ρ 1 = 𝟙 A.V :=
  by
  rw [MonoidHom.map_one]
  rfl
#align Action.ρ_one ActionCat.ρ_one

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : GroupCat.{u}} (A : ActionCat V (MonCat.of G)) : G ⟶ GroupCat.of (AutCat A.V)
    where
  toFun g :=
    { Hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id' := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one])
      inv_hom_id' := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]) }
  map_one' := by
    ext
    exact A.ρ.map_one
  map_mul' x y := by
    ext
    exact A.ρ.map_mul x y
#align Action.ρ_Aut ActionCat.ρAut

variable (G : MonCat.{u})

section

instance inhabited' : Inhabited (ActionCat (Type u) G) :=
  ⟨⟨PUnit, 1⟩⟩
#align Action.inhabited' ActionCat.inhabited'

/-- The trivial representation of a group. -/
def trivial : ActionCat AddCommGroupCat G
    where
  V := AddCommGroupCat.of PUnit
  ρ := 1
#align Action.trivial ActionCat.trivial

instance : Inhabited (ActionCat AddCommGroupCat G) :=
  ⟨trivial G⟩

end

variable {G V}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure Hom (M N : ActionCat V G) where
  Hom : M.V ⟶ N.V
  comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by obviously
#align Action.hom ActionCat.Hom

restate_axiom hom.comm'

namespace Hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : ActionCat V G) : ActionCat.Hom M M where Hom := 𝟙 M.V
#align Action.hom.id ActionCat.Hom.id

instance (M : ActionCat V G) : Inhabited (ActionCat.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : ActionCat V G} (p : ActionCat.Hom M N) (q : ActionCat.Hom N K) : ActionCat.Hom M K
    where
  Hom := p.Hom ≫ q.Hom
  comm' g := by rw [← category.assoc, p.comm, category.assoc, q.comm, ← category.assoc]
#align Action.hom.comp ActionCat.Hom.comp

end Hom

instance : Category (ActionCat V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp M N K f g := Hom.comp f g

@[simp]
theorem id_hom (M : ActionCat V G) : (𝟙 M : Hom M M).Hom = 𝟙 M.V :=
  rfl
#align Action.id_hom ActionCat.id_hom

@[simp]
theorem comp_hom {M N K : ActionCat V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Action.comp_hom ActionCat.comp_hom

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mkIso {M N : ActionCat V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.Hom = f.Hom ≫ N.ρ g) :
    M ≅ N
    where
  Hom :=
    { Hom := f.Hom
      comm' := comm }
  inv :=
    { Hom := f.inv
      comm' := fun g => by
        have w := comm g =≫ f.inv
        simp at w
        simp [w] }
#align Action.mk_iso ActionCat.mkIso

instance (priority := 100) isIso_of_hom_isIso {M N : ActionCat V G} (f : M ⟶ N) [IsIso f.Hom] :
    IsIso f := by
  convert is_iso.of_iso (mk_iso (as_iso f.hom) f.comm)
  ext
  rfl
#align Action.is_iso_of_hom_is_iso ActionCat.isIso_of_hom_isIso

instance isIso_hom_mk {M N : ActionCat V G} (f : M.V ⟶ N.V) [IsIso f] (w) : @IsIso _ _ M N ⟨f, w⟩ :=
  IsIso.of_iso (mkIso (asIso f) w)
#align Action.is_iso_hom_mk ActionCat.isIso_hom_mk

namespace FunctorCategoryEquivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : ActionCat V G ⥤ SingleObj G ⥤ V
    where
  obj M :=
    { obj := fun _ => M.V
      map := fun _ _ g => M.ρ g
      map_id' := fun _ => M.ρ.map_one
      map_comp' := fun _ _ _ g h => M.ρ.map_mul h g }
  map M N f :=
    { app := fun _ => f.Hom
      naturality' := fun _ _ g => f.comm g }
#align Action.functor_category_equivalence.functor ActionCat.FunctorCategoryEquivalence.functor

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ ActionCat V G
    where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map M N f :=
    { Hom := f.app PUnit.unit
      comm' := fun g => f.naturality g }
#align Action.functor_category_equivalence.inverse ActionCat.FunctorCategoryEquivalence.inverse

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def unitIso : 𝟭 (ActionCat V G) ≅ Functor ⋙ inverse :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.functor_category_equivalence.unit_iso ActionCat.FunctorCategoryEquivalence.unitIso

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def counitIso : inverse ⋙ Functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (by tidy) (by tidy)) (by tidy)
#align Action.functor_category_equivalence.counit_iso ActionCat.FunctorCategoryEquivalence.counitIso

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functorCategoryEquivalence : ActionCat V G ≌ SingleObj G ⥤ V
    where
  Functor := Functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
#align Action.functor_category_equivalence ActionCat.functorCategoryEquivalence

attribute [simps] functor_category_equivalence

instance [HasFiniteProducts V] : HasFiniteProducts (ActionCat V G)
    where out n :=
    Adjunction.hasLimitsOfShapeOfEquivalence (ActionCat.functorCategoryEquivalence _ _).Functor

instance [HasFiniteLimits V] : HasFiniteLimits (ActionCat V G)
    where out J _ _ :=
    adjunction.has_limits_of_shape_of_equivalence (ActionCat.functorCategoryEquivalence _ _).Functor

instance [HasLimits V] : HasLimits (ActionCat V G) :=
  Adjunction.hasLimitsOfEquivalence (ActionCat.functorCategoryEquivalence _ _).Functor

instance [HasColimits V] : HasColimits (ActionCat V G) :=
  Adjunction.hasColimitsOfEquivalence (ActionCat.functorCategoryEquivalence _ _).Functor

end

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
@[simps]
def forget : ActionCat V G ⥤ V where
  obj M := M.V
  map M N f := f.Hom
#align Action.forget ActionCat.forget

instance : Faithful (forget V G) where map_injective' X Y f g w := Hom.ext _ _ w

instance [ConcreteCategory V] : ConcreteCategory (ActionCat V G)
    where forget := forget V G ⋙ ConcreteCategory.forget V

instance hasForgetToV [ConcreteCategory V] : HasForget₂ (ActionCat V G) V
    where forget₂ := forget V G
#align Action.has_forget_to_V ActionCat.hasForgetToV

/-- The forgetful functor is intertwined by `functor_category_equivalence` with
evaluation at `punit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).Functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _
#align Action.functor_category_equivalence_comp_evaluation ActionCat.functorCategoryEquivalenceCompEvaluation

noncomputable instance [HasLimits V] : Limits.PreservesLimits (forget V G) :=
  Limits.preservesLimitsOfNatIso (ActionCat.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance [HasColimits V] : PreservesColimits (forget V G) :=
  preservesColimitsOfNatIso (ActionCat.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

theorem Iso.conj_ρ {M N : ActionCat V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) :=
  by
  rw [iso.conj_apply, iso.eq_inv_comp]
  simp [f.hom.comm']
#align Action.iso.conj_ρ ActionCat.Iso.conj_ρ

section HasZeroMorphisms

variable [HasZeroMorphisms V]

instance : HasZeroMorphisms (ActionCat V G)
    where
  HasZero X Y :=
    ⟨⟨0, by
        intro g
        simp⟩⟩
  comp_zero' P Q f R := by
    ext1
    simp
  zero_comp' P Q R f := by
    ext1
    simp

instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where
#align Action.forget_preserves_zero_morphisms ActionCat.forget_preservesZeroMorphisms

instance forget₂_preservesZeroMorphisms [ConcreteCategory V] :
    Functor.PreservesZeroMorphisms (forget₂ (ActionCat V G) V) where
#align Action.forget₂_preserves_zero_morphisms ActionCat.forget₂_preservesZeroMorphisms

instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_preserves_zero_morphisms ActionCat.functorCategoryEquivalence_preservesZeroMorphisms

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance : Preadditive (ActionCat V G)
    where
  homGroup X Y :=
    { zero := ⟨0, by simp⟩
      add := fun f g => ⟨f.Hom + g.Hom, by simp [f.comm, g.comm]⟩
      neg := fun f => ⟨-f.Hom, by simp [f.comm]⟩
      zero_add := by
        intros
        ext
        exact zero_add _
      add_zero := by
        intros
        ext
        exact add_zero _
      add_assoc := by
        intros
        ext
        exact add_assoc _ _ _
      add_left_neg := by
        intros
        ext
        exact add_left_neg _
      add_comm := by
        intros
        ext
        exact add_comm _ _ }
  add_comp' := by
    intros
    ext
    exact preadditive.add_comp _ _ _ _ _ _
  comp_add' := by
    intros
    ext
    exact preadditive.comp_add _ _ _ _ _ _

instance forget_additive : Functor.Additive (forget V G) where
#align Action.forget_additive ActionCat.forget_additive

instance forget₂_additive [ConcreteCategory V] : Functor.Additive (forget₂ (ActionCat V G) V) where
#align Action.forget₂_additive ActionCat.forget₂_additive

instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_additive ActionCat.functorCategoryEquivalence_additive

@[simp]
theorem zero_hom {X Y : ActionCat V G} : (0 : X ⟶ Y).Hom = 0 :=
  rfl
#align Action.zero_hom ActionCat.zero_hom

@[simp]
theorem neg_hom {X Y : ActionCat V G} (f : X ⟶ Y) : (-f).Hom = -f.Hom :=
  rfl
#align Action.neg_hom ActionCat.neg_hom

@[simp]
theorem add_hom {X Y : ActionCat V G} (f g : X ⟶ Y) : (f + g).Hom = f.Hom + g.Hom :=
  rfl
#align Action.add_hom ActionCat.add_hom

@[simp]
theorem sum_hom {X Y : ActionCat V G} {ι : Type _} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.Sum f).Hom = s.Sum fun i => (f i).Hom :=
  (forget V G).map_sum f s
#align Action.sum_hom ActionCat.sum_hom

end Preadditive

section Linear

variable [Preadditive V] {R : Type _} [Semiring R] [Linear R V]

instance : Linear R (ActionCat V G)
    where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.Hom, by simp [f.comm]⟩
      one_smul := by
        intros
        ext
        exact one_smul _ _
      smul_zero := by
        intros
        ext
        exact smul_zero _
      zero_smul := by
        intros
        ext
        exact zero_smul _ _
      add_smul := by
        intros
        ext
        exact add_smul _ _ _
      smul_add := by
        intros
        ext
        exact smul_add _ _ _
      mul_smul := by
        intros
        ext
        exact mul_smul _ _ _ }
  smul_comp' := by
    intros
    ext
    exact linear.smul_comp _ _ _ _ _ _
  comp_smul' := by
    intros
    ext
    exact linear.comp_smul _ _ _ _ _ _

instance forgetLinear : Functor.Linear R (forget V G) where
#align Action.forget_linear ActionCat.forgetLinear

instance forget₂Linear [ConcreteCategory V] : Functor.Linear R (forget₂ (ActionCat V G) V) where
#align Action.forget₂_linear ActionCat.forget₂Linear

instance functorCategoryEquivalenceLinear :
    Functor.Linear R (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_linear ActionCat.functorCategoryEquivalenceLinear

@[simp]
theorem smul_hom {X Y : ActionCat V G} (r : R) (f : X ⟶ Y) : (r • f).Hom = r • f.Hom :=
  rfl
#align Action.smul_hom ActionCat.smul_hom

end Linear

section Abelian

/-- Auxilliary construction for the `abelian (Action V G)` instance. -/
def abelianAux : ActionCat V G ≌ ULift.{u} (SingleObj G) ⥤ V :=
  (functorCategoryEquivalence V G).trans (Equivalence.congrLeft Ulift.equivalence)
#align Action.abelian_aux ActionCat.abelianAux

noncomputable instance [Abelian V] : Abelian (ActionCat V G) :=
  abelianOfEquivalence abelianAux.Functor

end Abelian

section Monoidal

variable [MonoidalCategory V]

instance : MonoidalCategory (ActionCat V G) :=
  Monoidal.transport (ActionCat.functorCategoryEquivalence _ _).symm

@[simp]
theorem tensorUnit_v : (𝟙_ (ActionCat V G)).V = 𝟙_ V :=
  rfl
#align Action.tensor_unit_V ActionCat.tensorUnit_v

@[simp]
theorem tensorUnit_rho {g : G} : (𝟙_ (ActionCat V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl
#align Action.tensor_unit_rho ActionCat.tensorUnit_rho

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_v {X Y : ActionCat V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl
#align Action.tensor_V ActionCat.tensor_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_rho {X Y : ActionCat V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl
#align Action.tensor_rho ActionCat.tensor_rho

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorHom {W X Y Z : ActionCat V G} (f : W ⟶ X) (g : Y ⟶ Z) : (f ⊗ g).Hom = f.Hom ⊗ g.Hom :=
  rfl
#align Action.tensor_hom ActionCat.tensorHom

@[simp]
theorem associator_hom_hom {X Y Z : ActionCat V G} :
    Hom.hom (α_ X Y Z).Hom = (α_ X.V Y.V Z.V).Hom :=
  by
  dsimp [monoidal.transport_associator]
  simp
#align Action.associator_hom_hom ActionCat.associator_hom_hom

@[simp]
theorem associator_inv_hom {X Y Z : ActionCat V G} :
    Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv :=
  by
  dsimp [monoidal.transport_associator]
  simp
#align Action.associator_inv_hom ActionCat.associator_inv_hom

@[simp]
theorem leftUnitor_hom_hom {X : ActionCat V G} : Hom.hom (λ_ X).Hom = (λ_ X.V).Hom :=
  by
  dsimp [monoidal.transport_left_unitor]
  simp
#align Action.left_unitor_hom_hom ActionCat.leftUnitor_hom_hom

@[simp]
theorem leftUnitor_inv_hom {X : ActionCat V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv :=
  by
  dsimp [monoidal.transport_left_unitor]
  simp
#align Action.left_unitor_inv_hom ActionCat.leftUnitor_inv_hom

@[simp]
theorem rightUnitor_hom_hom {X : ActionCat V G} : Hom.hom (ρ_ X).Hom = (ρ_ X.V).Hom :=
  by
  dsimp [monoidal.transport_right_unitor]
  simp
#align Action.right_unitor_hom_hom ActionCat.rightUnitor_hom_hom

@[simp]
theorem rightUnitor_inv_hom {X : ActionCat V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv :=
  by
  dsimp [monoidal.transport_right_unitor]
  simp
#align Action.right_unitor_inv_hom ActionCat.rightUnitor_inv_hom

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (ActionCat V G) V :=
  { ActionCat.forget _ _ with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }
#align Action.forget_monoidal ActionCat.forgetMonoidal

instance forgetMonoidal_faithful : Faithful (forgetMonoidal V G).toFunctor :=
  by
  change faithful (forget V G)
  infer_instance
#align Action.forget_monoidal_faithful ActionCat.forgetMonoidal_faithful

section

variable [BraidedCategory V]

instance : BraidedCategory (ActionCat V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _) (by tidy)) (by tidy)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps]
def forgetBraided : BraidedFunctor (ActionCat V G) V :=
  { forgetMonoidal _ _ with }
#align Action.forget_braided ActionCat.forgetBraided

instance forgetBraided_faithful : Faithful (forgetBraided V G).toFunctor :=
  by
  change faithful (forget V G)
  infer_instance
#align Action.forget_braided_faithful ActionCat.forgetBraided_faithful

end

instance [SymmetricCategory V] : SymmetricCategory (ActionCat V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance : MonoidalPreadditive (ActionCat V G) where

variable {R : Type _} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (ActionCat V G) where

end

variable (V G)

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (single_obj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (ActionCat V G) (SingleObj G ⥤ V) :=
  Monoidal.fromTransported (ActionCat.functorCategoryEquivalence _ _).symm
#align Action.functor_category_monoidal_equivalence ActionCat.functorCategoryMonoidalEquivalence

instance : IsEquivalence (functorCategoryMonoidalEquivalence V G).toFunctor :=
  by
  change is_equivalence (ActionCat.functorCategoryEquivalence _ _).Functor
  infer_instance

variable (H : GroupCat.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) :=
  by
  change right_rigid_category (single_obj H ⥤ V)
  infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (ActionCat V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) :=
  by
  change left_rigid_category (single_obj H ⥤ V)
  infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (ActionCat V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) :=
  by
  change rigid_category (single_obj H ⥤ V)
  infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (ActionCat V H) :=
  rigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

variable {V H} (X : ActionCat V H)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl
#align Action.right_dual_V ActionCat.rightDual_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl
#align Action.left_dual_V ActionCat.leftDual_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = X.ρ (h⁻¹ : H)ᘁ :=
  by
  rw [← single_obj.inv_as_inv]
  rfl
#align Action.right_dual_ρ ActionCat.rightDual_ρ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) :=
  by
  rw [← single_obj.inv_as_inv]
  rfl
#align Action.left_dual_ρ ActionCat.leftDual_ρ

end Monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def actionPunitEquivalence : ActionCat V (MonCat.of PUnit) ≌ V
    where
  Functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun X Y f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents (fun X => mkIso (Iso.refl _) fun ⟨⟩ => by simpa using ρ_one X) (by tidy)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align Action.Action_punit_equivalence ActionCat.actionPunitEquivalence

variable (V)

/-- The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : MonCat} (f : G ⟶ H) : ActionCat V H ⥤ ActionCat V G
    where
  obj M :=
    { V := M.V
      ρ := f ≫ M.ρ }
  map M N p :=
    { Hom := p.Hom
      comm' := fun g => p.comm (f g) }
#align Action.res ActionCat.res

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def resId {G : MonCat} : res V (𝟙 G) ≅ 𝟭 (ActionCat V G) :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.res_id ActionCat.resId

attribute [simps] res_id

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def resComp {G H K : MonCat} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.res_comp ActionCat.resComp

attribute [simps] res_comp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.
variable {G} {H : MonCat.{u}} (f : G ⟶ H)

instance res_additive [Preadditive V] : (res V f).Additive where
#align Action.res_additive ActionCat.res_additive

variable {R : Type _} [Semiring R]

instance resLinear [Preadditive V] [Linear R V] : (res V f).Linear R where
#align Action.res_linear ActionCat.resLinear

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G H : Type u) [Monoid G] [MulAction G H] : ActionCat (Type u) (MonCat.of G)
    where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)
#align Action.of_mul_action ActionCat.ofMulAction

@[simp]
theorem ofMulAction_apply {G H : Type u} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl
#align Action.of_mul_action_apply ActionCat.ofMulAction_apply

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `discrete_cases #[] -/
/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => ActionCat.ofMulAction G (F i))
    where
  Cone :=
    { x := ActionCat.ofMulAction G (∀ i : ι, F i)
      π :=
        { app := fun i => ⟨fun x => x i.as, fun g => by ext <;> rfl⟩
          naturality' := fun i j x => by
            ext
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `discrete_cases #[]"
            cases x
            congr } }
  IsLimit :=
    { lift := fun s =>
        { Hom := fun x i => (s.π.app ⟨i⟩).Hom x
          comm' := fun g => by
            ext (x j)
            dsimp
            exact congr_fun ((s.π.app ⟨j⟩).comm g) x }
      fac' := fun s j => by
        ext
        dsimp
        congr
        rw [discrete.mk_as]
      uniq' := fun s f h => by
        ext (x j)
        dsimp at *
        rw [← h ⟨j⟩]
        congr }
#align Action.of_mul_action_limit_cone ActionCat.ofMulActionLimitCone

end ActionCat

namespace CategoryTheory.Functor

variable {V} {W : Type (u + 1)} [LargeCategory W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : V ⥤ W) (G : MonCat.{u}) : ActionCat V G ⥤ ActionCat W G
    where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp only [End.one_def, ActionCat.ρ_one, F.map_id]
          map_mul' := fun g h => by simp only [End.mul_def, F.map_comp, map_mul] } }
  map M N f :=
    { Hom := F.map f.Hom
      comm' := fun g => by
        dsimp
        rw [← F.map_comp, f.comm, F.map_comp] }
  map_id' M := by
    ext
    simp only [ActionCat.id_hom, F.map_id]
  map_comp' M N P f g := by
    ext
    simp only [ActionCat.comp_hom, F.map_comp]
#align category_theory.functor.map_Action CategoryTheory.Functor.mapAction

variable (F : V ⥤ W) (G : MonCat.{u}) [Preadditive V] [Preadditive W]

instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where
#align category_theory.functor.map_Action_preadditive CategoryTheory.Functor.mapAction_preadditive

variable {R : Type _} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

instance mapActionLinear [F.Additive] [F.Linear R] : (F.mapAction G).Linear R where
#align category_theory.functor.map_Action_linear CategoryTheory.Functor.mapActionLinear

end CategoryTheory.Functor

namespace CategoryTheory.MonoidalFunctor

open ActionCat

variable {V} {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : MonoidalFunctor V W) (G : MonCat.{u}) :
    MonoidalFunctor (ActionCat V G) (ActionCat W G) :=
  {-- See note [dsimp, simp].
          F.toFunctor.mapAction
      G with
    ε :=
      { Hom := F.ε
        comm' := fun g => by
          dsimp
          erw [category.id_comp, CategoryTheory.Functor.map_id, category.comp_id] }
    μ := fun X Y =>
      { Hom := F.μ X.V Y.V
        comm' := fun g => F.toLaxMonoidalFunctor.μ_natural (X.ρ g) (Y.ρ g) }
    ε_is_iso := by infer_instance
    μ_is_iso := by infer_instance
    μ_natural' := by
      intros
      ext
      dsimp
      simp
    associativity' := by
      intros
      ext
      dsimp
      simp
      dsimp
      simp
    left_unitality' := by
      intros
      ext
      dsimp
      simp
      dsimp
      simp
    right_unitality' := by
      intros
      ext
      dsimp
      simp
      dsimp
      simp }
#align category_theory.monoidal_functor.map_Action CategoryTheory.MonoidalFunctor.mapAction

end CategoryTheory.MonoidalFunctor

