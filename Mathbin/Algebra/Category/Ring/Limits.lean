/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Ring.limits
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.RingTheory.Subring.Basic

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


-- We use the following trick a lot of times in this file.
library_note "change elaboration strategy with `by apply`"/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

namespace SemiRing

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ SemiRing.{max v u}) (j) : Semiring ((F ⋙ forget SemiRing).obj j) :=
  by
  change Semiring (F.obj j)
  infer_instance
#align SemiRing.semiring_obj SemiRing.semiringObj

/-- The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sectionsSubsemiring (F : J ⥤ SemiRing.{max v u}) : Subsemiring (∀ j, F.obj j) :=
  {
    AddMon.sectionsAddSubmonoid
      (F ⋙ forget₂ SemiRing AddCommMon.{max v u} ⋙ forget₂ AddCommMon AddMon.{max v u}),
    Mon.sectionsSubmonoid (F ⋙ forget₂ SemiRing Mon.{max v u}) with
    carrier := (F ⋙ forget SemiRing).sections }
#align SemiRing.sections_subsemiring SemiRing.sectionsSubsemiring

instance limitSemiring (F : J ⥤ SemiRing.{max v u}) :
    Semiring (Types.limitCone (F ⋙ forget SemiRing.{max v u})).x :=
  (sectionsSubsemiring F).toSemiring
#align SemiRing.limit_semiring SemiRing.limitSemiring

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limitπRingHom (F : J ⥤ SemiRing.{max v u}) (j) :
    (Types.limitCone (F ⋙ forget SemiRing)).x →+* (F ⋙ forget SemiRing).obj j :=
  {
    AddMon.limitπAddMonoidHom
      (F ⋙ forget₂ SemiRing AddCommMon.{max v u} ⋙ forget₂ AddCommMon AddMon.{max v u}) j,
    Mon.limitπMonoidHom (F ⋙ forget₂ SemiRing Mon.{max v u}) j with
    toFun := (Types.limitCone (F ⋙ forget SemiRing)).π.app j }
#align SemiRing.limit_π_ring_hom SemiRing.limitπRingHom

namespace HasLimits

-- The next two definitions are used in the construction of `has_limits SemiRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ SemiRing.{max v u}) : Cone F
    where
  x := SemiRing.of (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπRingHom F
      naturality' := fun j j' f =>
        RingHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align SemiRing.has_limits.limit_cone SemiRing.HasLimits.limitCone

/-- Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ SemiRing.{max v u}) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget SemiRing) (types.limit_cone_is_limit _)
        (fun s => ⟨_, _, _, _, _⟩) fun s => rfl <;>
    tidy
#align SemiRing.has_limits.limit_cone_is_limit SemiRing.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

/- ./././Mathport/Syntax/Translate/Command.lean:317:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v} SemiRing.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      {
        HasLimit := fun F =>
          has_limit.mk
            { Cone := limit_cone F
              IsLimit := limit_cone_is_limit F } } }
#align SemiRing.has_limits_of_size SemiRing.hasLimitsOfSize

instance hasLimits : HasLimits SemiRing.{u} :=
  SemiRing.hasLimitsOfSize.{u, u}
#align SemiRing.has_limits SemiRing.hasLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommMonPreservesLimitsAux (F : J ⥤ SemiRing.{max v u}) :
    IsLimit ((forget₂ SemiRing AddCommMon).mapCone (limitCone F)) := by
  apply AddCommMon.limit_cone_is_limit (F ⋙ forget₂ SemiRing AddCommMon.{max v u})
#align SemiRing.forget₂_AddCommMon_preserves_limits_aux SemiRing.forget₂AddCommMonPreservesLimitsAux

/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRing AddCommMon.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_AddCommMon_preserves_limits_aux F) }
#align SemiRing.forget₂_AddCommMon_preserves_limits_of_size SemiRing.forget₂AddCommMonPreservesLimitsOfSize

instance forget₂AddCommMonPreservesLimits : PreservesLimits (forget₂ SemiRing AddCommMon.{u}) :=
  SemiRing.forget₂AddCommMonPreservesLimitsOfSize.{u, u}
#align SemiRing.forget₂_AddCommMon_preserves_limits SemiRing.forget₂AddCommMonPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂MonPreservesLimitsAux (F : J ⥤ SemiRing.{max v u}) :
    IsLimit ((forget₂ SemiRing Mon).mapCone (limitCone F)) := by
  apply Mon.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRing Mon.{max v u})
#align SemiRing.forget₂_Mon_preserves_limits_aux SemiRing.forget₂MonPreservesLimitsAux

/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRing Mon.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_Mon_preserves_limits_aux F) }
#align SemiRing.forget₂_Mon_preserves_limits_of_size SemiRing.forget₂MonPreservesLimitsOfSize

instance forget₂MonPreservesLimits : PreservesLimits (forget₂ SemiRing Mon.{u}) :=
  SemiRing.forget₂MonPreservesLimitsOfSize.{u, u}
#align SemiRing.forget₂_Mon_preserves_limits SemiRing.forget₂MonPreservesLimits

/-- The forgetful functor from semirings to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget SemiRing.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align SemiRing.forget_preserves_limits_of_size SemiRing.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget SemiRing.{u}) :=
  SemiRing.forgetPreservesLimitsOfSize.{u, u}
#align SemiRing.forget_preserves_limits SemiRing.forgetPreservesLimits

end SemiRing

namespace CommSemiRing

variable {J : Type v} [SmallCategory J]

instance commSemiringObj (F : J ⥤ CommSemiRing.{max v u}) (j) :
    CommSemiring ((F ⋙ forget CommSemiRing).obj j) :=
  by
  change CommSemiring (F.obj j)
  infer_instance
#align CommSemiRing.comm_semiring_obj CommSemiRing.commSemiringObj

instance limitCommSemiring (F : J ⥤ CommSemiRing.{max v u}) :
    CommSemiring (Types.limitCone (F ⋙ forget CommSemiRing.{max v u})).x :=
  @Subsemiring.toCommSemiring (∀ j, F.obj j) _
    (SemiRing.sectionsSubsemiring (F ⋙ forget₂ CommSemiRing SemiRing.{max v u}))
#align CommSemiRing.limit_comm_semiring CommSemiRing.limitCommSemiring

/-- We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRing.{max v u}) :
    CreatesLimit F (forget₂ CommSemiRing SemiRing.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := CommSemiRing.of (Types.limitCone (F ⋙ forget _)).x
          π :=
            { app := by apply SemiRing.limitπRingHom (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})
              naturality' :=
                (SemiRing.HasLimits.limitCone
                      (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommSemiRing SemiRing.{max v u})
          (by apply SemiRing.HasLimits.limitConeIsLimit _)
          (fun s => (SemiRing.HasLimits.limitConeIsLimit _).lift ((forget₂ _ SemiRing).mapCone s))
          fun s => rfl }

/-- A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommSemiRing.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRing SemiRing.{max v u}))
#align CommSemiRing.limit_cone CommSemiRing.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommSemiRing.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommSemiRing.limit_cone_is_limit CommSemiRing.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:317:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} CommSemiRing.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ CommSemiRing SemiRing.{max v u}) } }
#align CommSemiRing.has_limits_of_size CommSemiRing.hasLimitsOfSize

instance hasLimits : HasLimits CommSemiRing.{u} :=
  CommSemiRing.hasLimitsOfSize.{u, u}
#align CommSemiRing.has_limits CommSemiRing.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommSemiRing SemiRing.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommSemiRing.forget₂_SemiRing_preserves_limits_of_size CommSemiRing.forget₂SemiRingPreservesLimitsOfSize

instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ CommSemiRing SemiRing.{u}) :=
  CommSemiRing.forget₂SemiRingPreservesLimitsOfSize.{u, u}
#align CommSemiRing.forget₂_SemiRing_preserves_limits CommSemiRing.forget₂SemiRingPreservesLimits

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommSemiRing.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommSemiRing SemiRing) (forget SemiRing) }
#align CommSemiRing.forget_preserves_limits_of_size CommSemiRing.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget CommSemiRing.{u}) :=
  CommSemiRing.forgetPreservesLimitsOfSize.{u, u}
#align CommSemiRing.forget_preserves_limits CommSemiRing.forgetPreservesLimits

end CommSemiRing

namespace RingCat

variable {J : Type v} [SmallCategory J]

instance ringObj (F : J ⥤ RingCat.{max v u}) (j) : Ring ((F ⋙ forget RingCat).obj j) :=
  by
  change Ring (F.obj j)
  infer_instance
#align Ring.ring_obj RingCat.ringObj

/-- The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sectionsSubring (F : J ⥤ RingCat.{max v u}) : Subring (∀ j, F.obj j) :=
  {
    AddGroupCat.sectionsAddSubgroup
      (F ⋙
        forget₂ RingCat AddCommGroupCat.{max v u} ⋙ forget₂ AddCommGroupCat AddGroupCat.{max v u}),
    SemiRing.sectionsSubsemiring (F ⋙ forget₂ RingCat SemiRing.{max v u}) with
    carrier := (F ⋙ forget RingCat).sections }
#align Ring.sections_subring RingCat.sectionsSubring

instance limitRing (F : J ⥤ RingCat.{max v u}) :
    Ring (Types.limitCone (F ⋙ forget RingCat.{max v u})).x :=
  (sectionsSubring F).toRing
#align Ring.limit_ring RingCat.limitRing

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ RingCat.{max v u}) : CreatesLimit F (forget₂ RingCat SemiRing.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := RingCat.of (Types.limitCone (F ⋙ forget _)).x
          π :=
            { app := by apply SemiRing.limitπRingHom (F ⋙ forget₂ RingCat SemiRing.{max v u})
              naturality' :=
                (SemiRing.HasLimits.limitCone
                      (F ⋙ forget₂ RingCat SemiRing.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRing.{max v u})
          (by apply SemiRing.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ RingCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat SemiRing.{max v u}))
#align Ring.limit_cone RingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ RingCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align Ring.limit_cone_is_limit RingCat.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:317:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} RingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ RingCat SemiRing.{max v u}) } }
#align Ring.has_limits_of_size RingCat.hasLimitsOfSize

instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}
#align Ring.has_limits RingCat.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat SemiRing.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align Ring.forget₂_SemiRing_preserves_limits_of_size RingCat.forget₂SemiRingPreservesLimitsOfSize

instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ RingCat SemiRing.{u}) :=
  RingCat.forget₂SemiRingPreservesLimitsOfSize.{u, u}
#align Ring.forget₂_SemiRing_preserves_limits RingCat.forget₂SemiRingPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ RingCat.{max v u}) :
    IsLimit ((forget₂ RingCat AddCommGroupCat).mapCone (limitCone F)) := by
  apply AddCommGroupCat.limit_cone_is_limit (F ⋙ forget₂ RingCat AddCommGroupCat.{max v u})
#align Ring.forget₂_AddCommGroup_preserves_limits_aux RingCat.forget₂AddCommGroupPreservesLimitsAux

/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat AddCommGroupCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_AddCommGroup_preserves_limits_aux F) }
#align Ring.forget₂_AddCommGroup_preserves_limits_of_size RingCat.forget₂AddCommGroupPreservesLimitsOfSize

instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGroupCat.{u}) :=
  RingCat.forget₂AddCommGroupPreservesLimitsOfSize.{u, u}
#align Ring.forget₂_AddCommGroup_preserves_limits RingCat.forget₂AddCommGroupPreservesLimits

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget RingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ RingCat SemiRing) (forget SemiRing.{max v u}) }
#align Ring.forget_preserves_limits_of_size RingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forgetPreservesLimitsOfSize.{u, u}
#align Ring.forget_preserves_limits RingCat.forgetPreservesLimits

end RingCat

namespace CommRingCat

variable {J : Type v} [SmallCategory J]

instance commRingObj (F : J ⥤ CommRingCat.{max v u}) (j) :
    CommRing ((F ⋙ forget CommRingCat).obj j) :=
  by
  change CommRing (F.obj j)
  infer_instance
#align CommRing.comm_ring_obj CommRingCat.commRingObj

instance limitCommRing (F : J ⥤ CommRingCat.{max v u}) :
    CommRing (Types.limitCone (F ⋙ forget CommRingCat.{max v u})).x :=
  @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
#align CommRing.limit_comm_ring CommRingCat.limitCommRing

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRingCat.{max v u}) : CreatesLimit F (forget₂ CommRingCat RingCat.{max v u}) :=
  /-
    A terse solution here would be
    ```
    creates_limit_of_fully_faithful_of_iso (CommRing.of (limit (F ⋙ forget _))) (iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    createsLimitOfReflectsIso
    fun c' t =>
    { liftedCone :=
        { x := CommRingCat.of (Types.limitCone (F ⋙ forget _)).x
          π :=
            { app := by
                apply
                  SemiRing.limitπRingHom
                    (F ⋙ forget₂ CommRingCat RingCat.{max v u} ⋙ forget₂ RingCat SemiRing.{max v u})
              naturality' :=
                (SemiRing.HasLimits.limitCone
                      (F ⋙
                        forget₂ _ RingCat.{max v u} ⋙
                          forget₂ _ SemiRing.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (RingCat.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{max v u})
          (by apply RingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
          (fun s => (RingCat.limitConeIsLimit _).lift ((forget₂ _ RingCat.{max v u}).mapCone s))
          fun s => rfl }

/-- A choice of limit cone for a functor into `CommRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommRingCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
#align CommRing.limit_cone CommRingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommRingCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommRing.limit_cone_is_limit CommRingCat.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:317:38: unsupported irreducible non-definition -/
/-- The category of commutative rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} CommRingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ CommRingCat RingCat.{max v u}) } }
#align CommRing.has_limits_of_size CommRingCat.hasLimitsOfSize

instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}
#align CommRing.has_limits CommRingCat.hasLimits

/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat RingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommRing.forget₂_Ring_preserves_limits_of_size CommRingCat.forget₂RingPreservesLimitsOfSize

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂RingPreservesLimitsOfSize.{u, u}
#align CommRing.forget₂_Ring_preserves_limits CommRingCat.forget₂RingPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux (F : J ⥤ CommRingCat.{max v u}) :
    IsLimit ((forget₂ CommRingCat CommSemiRing).mapCone (limitCone F)) := by
  apply CommSemiRing.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRing.{max v u})
#align CommRing.forget₂_CommSemiRing_preserves_limits_aux CommRingCat.forget₂CommSemiRingPreservesLimitsAux

/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat CommSemiRing.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_CommSemiRing_preserves_limits_aux F) }
#align CommRing.forget₂_CommSemiRing_preserves_limits_of_size CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize

instance forget₂CommSemiRingPreservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRing.{u}) :=
  CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize.{u, u}
#align CommRing.forget₂_CommSemiRing_preserves_limits CommRingCat.forget₂CommSemiRingPreservesLimits

/-- The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommRingCat RingCat) (forget RingCat) }
#align CommRing.forget_preserves_limits_of_size CommRingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forgetPreservesLimitsOfSize.{u, u}
#align CommRing.forget_preserves_limits CommRingCat.forgetPreservesLimits

end CommRingCat

