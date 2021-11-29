import Mathbin.Algebra.Ring.Pi 
import Mathbin.Algebra.Category.CommRing.Basic 
import Mathbin.Algebra.Category.Group.Limits 
import Mathbin.RingTheory.Subring.Basic

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/
library_note "change elaboration strategy with `by apply`"

open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable theory

namespace SemiRing

variable {J : Type u} [small_category J]

instance semiring_obj (F : J ⥤ SemiRing) j : Semiringₓ ((F ⋙ forget SemiRing).obj j) :=
  by 
    change Semiringₓ (F.obj j)
    infer_instance

/--
The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sections_subsemiring (F : J ⥤ SemiRing) : Subsemiring (∀ j, F.obj j) :=
  { AddMon.sectionsAddSubmonoid (F ⋙ forget₂ SemiRing AddCommMon ⋙ forget₂ AddCommMon AddMon),
    Mon.sectionsSubmonoid (F ⋙ forget₂ SemiRing Mon) with Carrier := (F ⋙ forget SemiRing).sections }

instance limit_semiring (F : J ⥤ SemiRing) : Semiringₓ (types.limit_cone (F ⋙ forget SemiRing.{u})).x :=
  (sections_subsemiring F).toSemiring

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limit_π_ring_hom (F : J ⥤ SemiRing.{u}) j :
  (types.limit_cone (F ⋙ forget SemiRing)).x →+* (F ⋙ forget SemiRing).obj j :=
  { AddMon.limitπAddMonoidHom (F ⋙ forget₂ SemiRing AddCommMon.{u} ⋙ forget₂ AddCommMon AddMon) j,
    Mon.limitπMonoidHom (F ⋙ forget₂ SemiRing Mon) j with toFun := (types.limit_cone (F ⋙ forget SemiRing)).π.app j }

namespace HasLimits

/--
Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ SemiRing.{u}) : cone F :=
  { x := SemiRing.of (types.limit_cone (F ⋙ forget _)).x,
    π :=
      { app := limit_π_ring_hom F,
        naturality' := fun j j' f => RingHom.coe_inj ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ SemiRing) : is_limit (limit_cone F) :=
  by 
    refine'
        is_limit.of_faithful (forget SemiRing) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _, _, _⟩) fun s => rfl <;>
      tidy

end HasLimits

open HasLimits

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits SemiRing :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommMon_preserves_limits_aux (F : J ⥤ SemiRing) :
  is_limit ((forget₂ SemiRing AddCommMon).mapCone (limit_cone F)) :=
  by 
    apply AddCommMon.limitConeIsLimit (F ⋙ forget₂ SemiRing AddCommMon)

/--
The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂_AddCommMon_preserves_limits : preserves_limits (forget₂ SemiRing AddCommMon) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (forget₂_AddCommMon_preserves_limits_aux F) } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_Mon_preserves_limits_aux (F : J ⥤ SemiRing) : is_limit ((forget₂ SemiRing Mon).mapCone (limit_cone F)) :=
  by 
    apply Mon.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRing Mon)

/--
The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ SemiRing Mon) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (forget₂_Mon_preserves_limits_aux F) } }

/--
The forgetful functor from semirings to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget SemiRing) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (types.limit_cone_is_limit (F ⋙ forget _)) } }

end SemiRing

namespace CommSemiRing

variable {J : Type u} [small_category J]

instance comm_semiring_obj (F : J ⥤ CommSemiRing) j : CommSemiringₓ ((F ⋙ forget CommSemiRing).obj j) :=
  by 
    change CommSemiringₓ (F.obj j)
    infer_instance

instance limit_comm_semiring (F : J ⥤ CommSemiRing) :
  CommSemiringₓ (types.limit_cone (F ⋙ forget CommSemiRing.{u})).x :=
  @Subsemiring.toCommSemiring (∀ j, F.obj j) _ (SemiRing.sectionsSubsemiring (F ⋙ forget₂ CommSemiRing SemiRing.{u}))

/--
We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRing) : creates_limit F (forget₂ CommSemiRing SemiRing.{u}) :=
  creates_limit_of_reflects_iso
    fun c' t =>
      { liftedCone :=
          { x := CommSemiRing.of (types.limit_cone (F ⋙ forget _)).x,
            π :=
              { app :=
                  by 
                    apply SemiRing.limitπRingHom (F ⋙ forget₂ CommSemiRing SemiRing),
                naturality' := (SemiRing.HasLimits.limitCone (F ⋙ forget₂ _ _)).π.naturality } },
        validLift :=
          by 
            apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t,
        makesLimit :=
          is_limit.of_faithful (forget₂ CommSemiRing SemiRing.{u})
            (by 
              apply SemiRing.HasLimits.limitConeIsLimit _)
            (fun s => (SemiRing.HasLimits.limitConeIsLimit _).lift ((forget₂ _ SemiRing).mapCone s)) fun s => rfl }

/--
A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ CommSemiRing) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ CommSemiRing SemiRing.{u}))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ CommSemiRing) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits CommSemiRing.{u} :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { HasLimit := fun F => has_limit_of_created F (forget₂ CommSemiRing SemiRing.{u}) } }

/--
The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂_SemiRing_preserves_limits : preserves_limits (forget₂ CommSemiRing SemiRing) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun F =>
              by 
                infer_instance } }

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommSemiRing) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F => limits.comp_preserves_limit (forget₂ CommSemiRing SemiRing) (forget SemiRing) } }

end CommSemiRing

namespace Ringₓₓ

variable {J : Type u} [small_category J]

instance ring_obj (F : J ⥤ Ringₓₓ) j : Ringₓ ((F ⋙ forget Ringₓₓ).obj j) :=
  by 
    change Ringₓ (F.obj j)
    infer_instance

/--
The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sections_subring (F : J ⥤ Ringₓₓ) : Subring (∀ j, F.obj j) :=
  { AddGroupₓₓ.sectionsAddSubgroup (F ⋙ forget₂ Ringₓₓ AddCommGroupₓₓ ⋙ forget₂ AddCommGroupₓₓ AddGroupₓₓ),
    SemiRing.sectionsSubsemiring (F ⋙ forget₂ Ringₓₓ SemiRing) with Carrier := (F ⋙ forget Ringₓₓ).sections }

instance limit_ring (F : J ⥤ Ringₓₓ) : Ringₓ (types.limit_cone (F ⋙ forget Ringₓₓ.{u})).x :=
  (sections_subring F).toRing

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ Ringₓₓ) : creates_limit F (forget₂ Ringₓₓ SemiRing.{u}) :=
  creates_limit_of_reflects_iso
    fun c' t =>
      { liftedCone :=
          { x := Ringₓₓ.of (types.limit_cone (F ⋙ forget _)).x,
            π :=
              { app :=
                  by 
                    apply SemiRing.limitπRingHom (F ⋙ forget₂ Ringₓₓ SemiRing),
                naturality' := (SemiRing.HasLimits.limitCone (F ⋙ forget₂ _ _)).π.naturality } },
        validLift :=
          by 
            apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t,
        makesLimit :=
          is_limit.of_faithful (forget₂ Ringₓₓ SemiRing.{u})
            (by 
              apply SemiRing.HasLimits.limitConeIsLimit _)
            (fun s => _) fun s => rfl }

/--
A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ Ringₓₓ) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ Ringₓₓ SemiRing.{u}))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ Ringₓₓ) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits Ringₓₓ :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { HasLimit := fun F => has_limit_of_created F (forget₂ Ringₓₓ SemiRing) } }

/--
The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂_SemiRing_preserves_limits : preserves_limits (forget₂ Ringₓₓ SemiRing) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun F =>
              by 
                infer_instance } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommGroup_preserves_limits_aux (F : J ⥤ Ringₓₓ) :
  is_limit ((forget₂ Ringₓₓ AddCommGroupₓₓ).mapCone (limit_cone F)) :=
  by 
    apply AddCommGroupₓₓ.limitConeIsLimit (F ⋙ forget₂ Ringₓₓ AddCommGroupₓₓ)

/--
The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits : preserves_limits (forget₂ Ringₓₓ AddCommGroupₓₓ) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (forget₂_AddCommGroup_preserves_limits_aux F) } }

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget Ringₓₓ) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ Ringₓₓ SemiRing) (forget SemiRing) } }

end Ringₓₓ

namespace CommRingₓₓ

variable {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRingₓₓ) j : CommRingₓ ((F ⋙ forget CommRingₓₓ).obj j) :=
  by 
    change CommRingₓ (F.obj j)
    infer_instance

instance limit_comm_ring (F : J ⥤ CommRingₓₓ) : CommRingₓ (types.limit_cone (F ⋙ forget CommRingₓₓ.{u})).x :=
  @Subring.toCommRing (∀ j, F.obj j) _ (Ringₓₓ.sectionsSubring (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{u}))

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRingₓₓ) : creates_limit F (forget₂ CommRingₓₓ Ringₓₓ.{u}) :=
  creates_limit_of_reflects_iso
    fun c' t =>
      { liftedCone :=
          { x := CommRingₓₓ.of (types.limit_cone (F ⋙ forget _)).x,
            π :=
              { app :=
                  by 
                    apply SemiRing.limitπRingHom (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{u} ⋙ forget₂ Ringₓₓ SemiRing),
                naturality' :=
                  (SemiRing.HasLimits.limitCone (F ⋙ forget₂ _ Ringₓₓ.{u} ⋙ forget₂ _ SemiRing)).π.naturality } },
        validLift :=
          by 
            apply is_limit.unique_up_to_iso (Ringₓₓ.limitConeIsLimit _) t,
        makesLimit :=
          is_limit.of_faithful (forget₂ _ Ringₓₓ.{u})
            (by 
              apply Ringₓₓ.limitConeIsLimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ))
            (fun s => (Ringₓₓ.limitConeIsLimit _).lift ((forget₂ _ Ringₓₓ.{u}).mapCone s)) fun s => rfl }

/--
A choice of limit cone for a functor into `CommRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ CommRingₓₓ) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{u}))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ CommRingₓₓ) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

/-- The category of commutative rings has all limits. -/
@[irreducible]
instance has_limits : has_limits CommRingₓₓ.{u} :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { HasLimit := fun F => has_limit_of_created F (forget₂ CommRingₓₓ Ringₓₓ.{u}) } }

/--
The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ CommRingₓₓ Ringₓₓ) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun F =>
              by 
                infer_instance } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_CommSemiRing_preserves_limits_aux (F : J ⥤ CommRingₓₓ) :
  is_limit ((forget₂ CommRingₓₓ CommSemiRing).mapCone (limit_cone F)) :=
  by 
    apply CommSemiRing.limitConeIsLimit (F ⋙ forget₂ CommRingₓₓ CommSemiRing)

/--
The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂_CommSemiRing_preserves_limits : preserves_limits (forget₂ CommRingₓₓ CommSemiRing) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (forget₂_CommSemiRing_preserves_limits_aux F) } }

/--
The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommRingₓₓ) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommRingₓₓ Ringₓₓ) (forget Ringₓₓ) } }

end CommRingₓₓ

