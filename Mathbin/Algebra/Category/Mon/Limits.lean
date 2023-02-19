/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.limits
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

universe v u

namespace Mon

variable {J : Type v} [SmallCategory J]

@[to_additive]
instance monoidObj (F : J ⥤ Mon.{max v u}) (j) : Monoid ((F ⋙ forget Mon).obj j) :=
  by
  change Monoid (F.obj j)
  infer_instance
#align Mon.monoid_obj Mon.monoidObj
#align AddMon.add_monoid_obj AddMon.addMonoidObj

/-- The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive
      "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sectionsSubmonoid (F : J ⥤ Mon.{max v u}) : Submonoid (∀ j, F.obj j)
    where
  carrier := (F ⋙ forget Mon).sections
  one_mem' j j' f := by simp
  mul_mem' a b ah bh j j' f :=
    by
    simp only [forget_map_eq_coe, functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
    dsimp [functor.sections] at ah bh
    rw [ah f, bh f]
#align Mon.sections_submonoid Mon.sectionsSubmonoid
#align AddMon.sections_add_submonoid AddMon.sectionsAddSubmonoid

@[to_additive]
instance limitMonoid (F : J ⥤ Mon.{max v u}) :
    Monoid (Types.limitCone (F ⋙ forget Mon.{max v u})).x :=
  (sectionsSubmonoid F).toMonoid
#align Mon.limit_monoid Mon.limitMonoid
#align AddMon.limit_add_monoid AddMon.limitAddMonoid

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limitπMonoidHom (F : J ⥤ Mon.{max v u}) (j) :
    (Types.limitCone (F ⋙ forget Mon)).x →* (F ⋙ forget Mon).obj j
    where
  toFun := (Types.limitCone (F ⋙ forget Mon)).π.app j
  map_one' := rfl
  map_mul' x y := rfl
#align Mon.limit_π_monoid_hom Mon.limitπMonoidHom
#align AddMon.limit_π_add_monoid_hom AddMon.limitπAddMonoidHom

namespace HasLimits

-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limitCone (F : J ⥤ Mon.{max v u}) : Cone F
    where
  x := Mon.of (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπMonoidHom F
      naturality' := fun j j' f =>
        MonoidHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Mon.has_limits.limit_cone Mon.HasLimits.limitCone
#align AddMon.has_limits.limit_cone AddMon.HasLimits.limitCone

/-- Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limitConeIsLimit (F : J ⥤ Mon.{max v u}) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget Mon) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩) fun s =>
        rfl <;>
    tidy
#align Mon.has_limits.limit_cone_is_limit Mon.HasLimits.limitConeIsLimit
#align AddMon.has_limits.limit_cone_is_limit AddMon.HasLimits.limit_cone_is_limit

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive "The category of additive monoids has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v} Mon.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    {
      HasLimit := fun F =>
        has_limit.mk
          { Cone := limit_cone F
            IsLimit := limit_cone_is_limit F } }
#align Mon.has_limits_of_size Mon.hasLimitsOfSize
#align AddMon.has_limits_of_size AddMon.has_limits_of_size

@[to_additive]
instance hasLimits : HasLimits Mon.{u} :=
  Mon.hasLimitsOfSize.{u, u}
#align Mon.has_limits Mon.hasLimits
#align AddMon.has_limits AddMon.hasLimits

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive monoids to types preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v} (forget Mon.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align Mon.forget_preserves_limits_of_size Mon.forgetPreservesLimitsOfSize
#align AddMon.forget_preserves_limits_of_size AddMon.forget_preserves_limits_of_size

@[to_additive]
instance forgetPreservesLimits : PreservesLimits (forget Mon.{u}) :=
  Mon.forgetPreservesLimitsOfSize.{u, u}
#align Mon.forget_preserves_limits Mon.forgetPreservesLimits
#align AddMon.forget_preserves_limits AddMon.forgetPreservesLimits

end Mon

namespace CommMon

variable {J : Type v} [SmallCategory J]

@[to_additive]
instance commMonoidObj (F : J ⥤ CommMon.{max v u}) (j) : CommMonoid ((F ⋙ forget CommMon).obj j) :=
  by
  change CommMonoid (F.obj j)
  infer_instance
#align CommMon.comm_monoid_obj CommMon.commMonoidObj
#align AddCommMon.add_comm_monoid_obj AddCommMon.addCommMonoidObj

@[to_additive]
instance limitCommMonoid (F : J ⥤ CommMon.{max v u}) :
    CommMonoid (Types.limitCone (F ⋙ forget CommMon.{max v u})).x :=
  @Submonoid.toCommMonoid (∀ j, F.obj j) _
    (Mon.sectionsSubmonoid (F ⋙ forget₂ CommMon Mon.{max v u}))
#align CommMon.limit_comm_monoid CommMon.limitCommMonoid
#align AddCommMon.limit_add_comm_monoid AddCommMon.limitAddCommMonoid

/-- We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit. -/
@[to_additive
      "We show that the forgetful functor `AddCommMon ⥤ AddMon` creates limits.\n\nAll we need to do is notice that the limit point has an `add_comm_monoid` instance available,\nand then reuse the existing limit."]
instance (F : J ⥤ CommMon.{max v u}) : CreatesLimit F (forget₂ CommMon Mon.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := CommMon.of (Types.limitCone (F ⋙ forget CommMon)).x
          π :=
            { app := Mon.limitπMonoidHom (F ⋙ forget₂ CommMon Mon.{max v u})
              naturality' :=
                (Mon.HasLimits.limitCone (F ⋙ forget₂ CommMon Mon.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (Mon.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMon Mon.{max v u}) (Mon.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `CommMon`. (Generally, you'll just want\nto use `limit F`.)"]
def limitCone (F : J ⥤ CommMon.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMon Mon.{max v u}))
#align CommMon.limit_cone CommMon.limitCone
#align AddCommMon.limit_cone AddCommMon.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ CommMon.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommMon.limit_cone_is_limit CommMon.limitConeIsLimit
#align AddCommMon.limit_cone_is_limit AddCommMon.limit_cone_is_limit

/-- The category of commutative monoids has all limits. -/
@[to_additive "The category of commutative monoids has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommMon.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F => has_limit_of_created F (forget₂ CommMon Mon.{max v u}) }
#align CommMon.has_limits_of_size CommMon.hasLimitsOfSize
#align AddCommMon.has_limits_of_size AddCommMon.has_limits_of_size

@[to_additive]
instance hasLimits : HasLimits CommMon.{u} :=
  CommMon.hasLimitsOfSize.{u, u}
#align CommMon.has_limits CommMon.hasLimits
#align AddCommMon.has_limits AddCommMon.hasLimits

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMon.forget₂_AddMon_preserves_limits
      "The forgetful functor from additive\ncommutative monoids to additive monoids preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of additive\nmonoids."]
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommMon Mon.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommMon.forget₂_Mon_preserves_limits_of_size CommMon.forget₂MonPreservesLimitsOfSize
#align AddCommMon.forget₂_AddMon_preserves_limits AddCommMon.forget₂_AddMon_preserves_limits

@[to_additive]
instance forget₂MonPreservesLimits : PreservesLimits (forget₂ CommMon Mon.{u}) :=
  CommMon.forget₂MonPreservesLimitsOfSize.{u, u}
#align CommMon.forget₂_Mon_preserves_limits CommMon.forget₂MonPreservesLimits
#align AddCommMon.forget₂_Mon_preserves_limits AddCommMon.forget₂MonPreservesLimits

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive commutative monoids to types preserves all\nlimits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommMon.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommMon Mon) (forget Mon) }
#align CommMon.forget_preserves_limits_of_size CommMon.forgetPreservesLimitsOfSize
#align AddCommMon.forget_preserves_limits_of_size AddCommMon.forget_preserves_limits_of_size

@[to_additive]
instance forgetPreservesLimits : PreservesLimits (forget CommMon.{u}) :=
  CommMon.forgetPreservesLimitsOfSize.{u, u}
#align CommMon.forget_preserves_limits CommMon.forgetPreservesLimits
#align AddCommMon.forget_preserves_limits AddCommMon.forgetPreservesLimits

end CommMon

