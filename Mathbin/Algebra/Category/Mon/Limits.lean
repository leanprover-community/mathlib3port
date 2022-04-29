/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.Algebra.Group.Pi
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.GroupTheory.Submonoid.Operations

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe u

namespace Mon

variable {J : Type u} [SmallCategory J]

@[to_additive]
instance monoidObj (F : J ⥤ Mon) j : Monoidₓ ((F ⋙ forget Mon).obj j) := by
  change Monoidₓ (F.obj j)
  infer_instance

/-- The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sectionsSubmonoid (F : J ⥤ Mon) : Submonoid (∀ j, F.obj j) where
  Carrier := (F ⋙ forget Mon).sections
  one_mem' := fun j j' f => by
    simp
  mul_mem' := fun a b ah bh j j' f => by
    simp only [forget_map_eq_coe, functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
    dsimp [functor.sections]  at ah bh
    rw [ah f, bh f]

@[to_additive]
instance limitMonoid (F : J ⥤ Mon) : Monoidₓ (Types.limitCone (F ⋙ forget Mon.{u})).x :=
  (sectionsSubmonoid F).toMonoid

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limitπMonoidHom (F : J ⥤ Mon.{u}) j : (Types.limitCone (F ⋙ forget Mon)).x →* (F ⋙ forget Mon).obj j where
  toFun := (Types.limitCone (F ⋙ forget Mon)).π.app j
  map_one' := rfl
  map_mul' := fun x y => rfl

namespace HasLimits

/-- Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
@[to_additive "(Internal use only; use the limits API.)"]
def limitCone (F : J ⥤ Mon.{u}) : Cone F where
  x := Mon.of (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπMonoidHom F,
      naturality' := fun j j' f => MonoidHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limitConeIsLimit (F : J ⥤ Mon) : IsLimit (limitCone F) := by
  refine' is_limit.of_faithful (forget Mon) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩) fun s => rfl <;> tidy

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive "The category of additive monoids has all limits."]
instance has_limits : HasLimits Mon where
  HasLimitsOfShape := fun J 𝒥 =>
    { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } }

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive monoids to types preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimits : PreservesLimits (forget Mon) where
  PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) }

end Mon

namespace CommMon

variable {J : Type u} [SmallCategory J]

@[to_additive]
instance commMonoidObj (F : J ⥤ CommMon) j : CommMonoidₓ ((F ⋙ forget CommMon).obj j) := by
  change CommMonoidₓ (F.obj j)
  infer_instance

@[to_additive]
instance limitCommMonoid (F : J ⥤ CommMon) : CommMonoidₓ (Types.limitCone (F ⋙ forget CommMon.{u})).x :=
  @Submonoid.toCommMonoid (∀ j, F.obj j) _ (Mon.sectionsSubmonoid (F ⋙ forget₂ CommMon Mon.{u}))

/-- We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit. -/
@[to_additive
      "We show that the forgetful functor `AddCommMon ⥤ AddMon` creates limits.\n\nAll we need to do is notice that the limit point has an `add_comm_monoid` instance available,\nand then reuse the existing limit."]
instance (F : J ⥤ CommMon) : CreatesLimit F (forget₂ CommMon Mon.{u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := CommMon.of (Types.limitCone (F ⋙ forget CommMon)).x,
          π :=
            { app := Mon.limitπMonoidHom (F ⋙ forget₂ CommMon Mon),
              naturality' := (Mon.HasLimits.limitCone (F ⋙ forget₂ _ _)).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (Mon.HasLimits.limitConeIsLimit _) t,
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMon Mon.{u}) (Mon.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `CommMon`. (Generally, you'll just want\nto use `limit F`.)"]
def limitCone (F : J ⥤ CommMon) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMon Mon.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ CommMon) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- The category of commutative monoids has all limits. -/
@[to_additive "The category of commutative monoids has all limits."]
instance has_limits : HasLimits CommMon where
  HasLimitsOfShape := fun J 𝒥 => { HasLimit := fun F => has_limit_of_created F (forget₂ CommMon Mon) }

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMon.forget₂AddMonPreservesLimits
      "The forgetful functor from additive\ncommutative monoids to additive monoids preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of additive\nmonoids."]
instance forget₂MonPreservesLimits : PreservesLimits (forget₂ CommMon Mon) where
  PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => by
        infer_instance }

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive commutative monoids to types preserves all\nlimits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimits : PreservesLimits (forget CommMon) where
  PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommMon Mon) (forget Mon) }

end CommMon

