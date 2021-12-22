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

variable {J : Type u} [small_category J]

@[to_additive]
instance monoid_obj (F : J ⥤ Mon) j : Monoidₓ ((F ⋙ forget Mon).obj j) := by
  change Monoidₓ (F.obj j)
  infer_instance

/-- 
The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sections_submonoid (F : J ⥤ Mon) : Submonoid (∀ j, F.obj j) :=
  { Carrier := (F ⋙ forget Mon).sections,
    one_mem' := fun j j' f => by
      simp ,
    mul_mem' := fun a b ah bh j j' f => by
      simp only [forget_map_eq_coe, functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
      dsimp [functor.sections]  at ah bh
      rw [ah f, bh f] }

@[to_additive]
instance limit_monoid (F : J ⥤ Mon) : Monoidₓ (types.limit_cone (F ⋙ forget Mon.{u})).x :=
  (sections_submonoid F).toMonoid

/--  `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limit_π_monoid_hom (F : J ⥤ Mon.{u}) j : (types.limit_cone (F ⋙ forget Mon)).x →* (F ⋙ forget Mon).obj j :=
  { toFun := (types.limit_cone (F ⋙ forget Mon)).π.app j, map_one' := rfl, map_mul' := fun x y => rfl }

namespace HasLimits

/-- 
Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limit_cone (F : J ⥤ Mon.{u}) : cone F :=
  { x := Mon.of (types.limit_cone (F ⋙ forget _)).x,
    π :=
      { app := limit_π_monoid_hom F,
        naturality' := fun j j' f => MonoidHom.coe_inj ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/-- 
Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limit_cone_is_limit (F : J ⥤ Mon) : is_limit (limit_cone F) := by
  refine' is_limit.of_faithful (forget Mon) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩) fun s => rfl <;> tidy

end HasLimits

open HasLimits

-- failed to format: format: uncaught backtrack exception
/-- The category of monoids has all limits. -/ @[ to_additive ]
  instance
    has_limits
    : has_limits Mon
    where
      HasLimitsOfShape
        J 𝒥
        :=
        by exact { HasLimit := fun F => has_limit.mk { Cone := limit_cone F , IsLimit := limit_cone_is_limit F } }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from monoids to types preserves all limits. (That is, the underlying
      types could have been computed instead as limits in the category of types.)
      -/
    @[ to_additive ]
  instance
    forget_preserves_limits
    : preserves_limits ( forget Mon )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by
          exact
            {
              PreservesLimit
                :=
                fun
                  F
                    =>
                    preserves_limit_of_preserves_limit_cone
                      ( limit_cone_is_limit F ) ( types.limit_cone_is_limit ( F ⋙ forget _ ) )
              }

end Mon

namespace CommMon

variable {J : Type u} [small_category J]

@[to_additive]
instance comm_monoid_obj (F : J ⥤ CommMon) j : CommMonoidₓ ((F ⋙ forget CommMon).obj j) := by
  change CommMonoidₓ (F.obj j)
  infer_instance

@[to_additive]
instance limit_comm_monoid (F : J ⥤ CommMon) : CommMonoidₓ (types.limit_cone (F ⋙ forget CommMon.{u})).x :=
  @Submonoid.toCommMonoid (∀ j, F.obj j) _ (Mon.sectionsSubmonoid (F ⋙ forget₂ CommMon Mon.{u}))

/-- 
We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit.
-/
@[to_additive]
instance (F : J ⥤ CommMon) : creates_limit F (forget₂ CommMon Mon.{u}) :=
  creates_limit_of_reflects_iso fun c' t =>
    { liftedCone :=
        { x := CommMon.of (types.limit_cone (F ⋙ forget CommMon)).x,
          π :=
            { app := Mon.limitπMonoidHom (F ⋙ forget₂ CommMon Mon),
              naturality' := (Mon.HasLimits.limitCone (F ⋙ forget₂ _ _)).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (Mon.HasLimits.limitConeIsLimit _) t,
      makesLimit :=
        is_limit.of_faithful (forget₂ CommMon Mon.{u}) (Mon.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- 
A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `CommMon`. (Generally, you'll just want\nto use `limit F`.)"]
def limit_cone (F : J ⥤ CommMon) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ CommMon Mon.{u}))

/-- 
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ CommMon) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

-- failed to format: format: uncaught backtrack exception
/-- The category of commutative monoids has all limits. -/ @[ to_additive ]
  instance
    has_limits
    : has_limits CommMon
    where HasLimitsOfShape J 𝒥 := by exact { HasLimit := fun F => has_limit_of_created F ( forget₂ CommMon Mon ) }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from commutative monoids to monoids preserves all limits.
      (That is, the underlying monoid could have been computed instead as limits in the category
      of monoids.)
      -/
    @[ to_additive AddCommMon.forget₂AddMonPreservesLimits ]
  instance
    forget₂_Mon_preserves_limits
    : preserves_limits ( forget₂ CommMon Mon )
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from commutative monoids to types preserves all limits. (That is, the
      underlying types could have been computed instead as limits in the category of types.)
      -/
    @[ to_additive ]
  instance
    forget_preserves_limits
    : preserves_limits ( forget CommMon )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by exact { PreservesLimit := fun F => limits.comp_preserves_limit ( forget₂ CommMon Mon ) ( forget Mon ) }

end CommMon

