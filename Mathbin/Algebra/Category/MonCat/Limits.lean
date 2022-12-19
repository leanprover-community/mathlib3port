/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.limits
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.MonCat.Basic
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

namespace MonCat

variable {J : Type v} [SmallCategory J]

@[to_additive]
instance monoidObj (F : J ⥤ MonCat.{max v u}) (j) : Monoid ((F ⋙ forget MonCat).obj j) := by
  change Monoid (F.obj j)
  infer_instance
#align Mon.monoid_obj MonCat.monoidObj

/-- The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive
      "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sectionsSubmonoid (F : J ⥤ MonCat.{max v u}) :
    Submonoid (∀ j, F.obj
          j) where 
  carrier := (F ⋙ forget MonCat).sections
  one_mem' j j' f := by simp
  mul_mem' a b ah bh j j' f := by
    simp only [forget_map_eq_coe, functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
    dsimp [functor.sections] at ah bh
    rw [ah f, bh f]
#align Mon.sections_submonoid MonCat.sectionsSubmonoid

@[to_additive]
instance limitMonoid (F : J ⥤ MonCat.{max v u}) :
    Monoid (Types.limitCone (F ⋙ forget MonCat.{max v u})).x :=
  (sectionsSubmonoid F).toMonoid
#align Mon.limit_monoid MonCat.limitMonoid

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limitπMonoidHom (F : J ⥤ MonCat.{max v u}) (j) :
    (Types.limitCone (F ⋙ forget MonCat)).x →*
      (F ⋙ forget MonCat).obj
        j where 
  toFun := (Types.limitCone (F ⋙ forget MonCat)).π.app j
  map_one' := rfl
  map_mul' x y := rfl
#align Mon.limit_π_monoid_hom MonCat.limitπMonoidHom

namespace HasLimits

-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limitCone (F : J ⥤ MonCat.{max v u}) :
    Cone F where 
  x := MonCat.of (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπMonoidHom F
      naturality' := fun j j' f =>
        MonoidHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Mon.has_limits.limit_cone MonCat.HasLimits.limitCone

/-- Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limitConeIsLimit (F : J ⥤ MonCat.{max v u}) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget MonCat) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩)
        fun s => rfl <;>
    tidy
#align Mon.has_limits.limit_cone_is_limit MonCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive "The category of additive monoids has all limits."]
instance hasLimitsOfSize :
    HasLimitsOfSize.{v}
      MonCat.{max v
          u} where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F =>
        has_limit.mk
          { Cone := limit_cone F
            IsLimit := limit_cone_is_limit F } }
#align Mon.has_limits_of_size MonCat.hasLimitsOfSize

@[to_additive]
instance has_limits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}
#align Mon.has_limits MonCat.has_limits

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive monoids to types preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v}
      (forget
        MonCat.{max v
            u}) where PreservesLimitsOfShape J 𝒥 :=
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align Mon.forget_preserves_limits_of_size MonCat.forgetPreservesLimitsOfSize

@[to_additive]
instance forgetPreservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forgetPreservesLimitsOfSize.{u, u}
#align Mon.forget_preserves_limits MonCat.forgetPreservesLimits

end MonCat

namespace CommMonCat

variable {J : Type v} [SmallCategory J]

@[to_additive]
instance commMonoidObj (F : J ⥤ CommMonCat.{max v u}) (j) :
    CommMonoid ((F ⋙ forget CommMonCat).obj j) := by
  change CommMonoid (F.obj j)
  infer_instance
#align CommMon.comm_monoid_obj CommMonCat.commMonoidObj

@[to_additive]
instance limitCommMonoid (F : J ⥤ CommMonCat.{max v u}) :
    CommMonoid (Types.limitCone (F ⋙ forget CommMonCat.{max v u})).x :=
  @Submonoid.toCommMonoid (∀ j, F.obj j) _
    (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat MonCat.{max v u}))
#align CommMon.limit_comm_monoid CommMonCat.limitCommMonoid

/-- We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit. -/
@[to_additive
      "We show that the forgetful functor `AddCommMon ⥤ AddMon` creates limits.\n\nAll we need to do is notice that the limit point has an `add_comm_monoid` instance available,\nand then reuse the existing limit."]
instance (F : J ⥤ CommMonCat.{max v u}) : CreatesLimit F (forget₂ CommMonCat MonCat.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := CommMonCat.of (Types.limitCone (F ⋙ forget CommMonCat)).x
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat MonCat.{max v u})
              naturality' :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ CommMonCat MonCat.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMonCat MonCat.{max v u})
          (MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `CommMon`. (Generally, you'll just want\nto use `limit F`.)"]
def limitCone (F : J ⥤ CommMonCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat MonCat.{max v u}))
#align CommMon.limit_cone CommMonCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ CommMonCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommMon.limit_cone_is_limit CommMonCat.limitConeIsLimit

/-- The category of commutative monoids has all limits. -/
@[to_additive "The category of commutative monoids has all limits."]
instance hasLimitsOfSize :
    HasLimitsOfSize.{v, v}
      CommMonCat.{max v
          u} where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F => has_limit_of_created F (forget₂ CommMonCat MonCat.{max v u}) }
#align CommMon.has_limits_of_size CommMonCat.hasLimitsOfSize

@[to_additive]
instance has_limits : HasLimits CommMonCat.{u} :=
  CommMonCat.hasLimitsOfSize.{u, u}
#align CommMon.has_limits CommMonCat.has_limits

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMonCat.forget₂AddMonPreservesLimits
      "The forgetful functor from additive\ncommutative monoids to additive monoids preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of additive\nmonoids."]
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ CommMonCat
        MonCat.{max v
            u}) where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommMon.forget₂_Mon_preserves_limits_of_size CommMonCat.forget₂MonPreservesLimitsOfSize

@[to_additive]
instance forget₂MonPreservesLimits : PreservesLimits (forget₂ CommMonCat MonCat.{u}) :=
  CommMonCat.forget₂MonPreservesLimitsOfSize.{u, u}
#align CommMon.forget₂_Mon_preserves_limits CommMonCat.forget₂MonPreservesLimits

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive commutative monoids to types preserves all\nlimits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        CommMonCat.{max v
            u}) where PreservesLimitsOfShape J 𝒥 :=
    { PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommMonCat MonCat) (forget MonCat) }
#align CommMon.forget_preserves_limits_of_size CommMonCat.forgetPreservesLimitsOfSize

@[to_additive]
instance forgetPreservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forgetPreservesLimitsOfSize.{u, u}
#align CommMon.forget_preserves_limits CommMonCat.forgetPreservesLimits

end CommMonCat

